package uclid.smt

import org.scalatest.{FlatSpec, Matchers}

class Btor2Spec extends FlatSpec with Matchers {

  // this function actually parses, serializes and parses again
  // in order to also test the serialization
  def parse(src: Seq[String]): SymbolicTransitionSystem = {
    val sys0 = Btor2.read(src.toIterator)
    val src1 = Btor2.serialize(sys0)
    val sys1 = Btor2.read(src1.toIterator)
    sys1
  }

  "single bool state" should "be parsed correctly" in {
    val sys = parse(Seq("1 sort bitvec 1", "2 state 1 test"))
    sys.inputs.isEmpty should be (true)
    sys.states.head.sym.id should be ("test")
    sys.states.head.sym.typ should be (BoolType)
  }

  "single bitvector state" should "be parsed correctly" in {
    val sys = parse(Seq("1 sort bitvec 3", "2 state 1 test"))
    sys.states.head.sym.typ should be (BitVectorType(3))
  }

  "single array state" should "be parsed correctly" in {
    val sys = parse(Seq("1 sort bitvec 3", "2 sort array 1 1", "3 state 2 test"))
    val bv3 = BitVectorType(3)
    sys.states.head.sym.typ should be (ArrayType(List(bv3), bv3))
  }

  def parse_res(src: Seq[String]): Expr = {
    val sys = parse(src)
    require(sys.outputs.length == 1)
    sys.outputs.head._2
  }

  "mul expressions" should "be parsed correctly" in {
    val e = parse_res(Seq("1 sort bitvec 1", "2 const 1 1", "3 const 1 0", "4 mul 1 2 3", "5 output 4"))
    e should be (OperatorApplication(ConjunctionOp, List(BooleanLit(true), BooleanLit(false))))
  }

  // this example if from the official btor2tools repository
  "count2" should "be parsed correctly" in {
    val count2 =
      """
        |1 sort bitvec 3
        |2 zero 1
        |3 state 1
        |4 init 1 3 2
        |5 one 1
        |6 add 1 3 5
        |7 next 1 3 6
        |8 ones 1
        |9 sort bitvec 1
        |10 eq 9 3 8
        |11 bad 10
        |""".stripMargin.split("\n")

    val sys = parse(count2)
    val s0 = sys.states.head
    s0.sym.id should be ("_state_0")
    s0.init should be (Some(BitVectorLit(0, 3)))
    s0.next should be (Some(OperatorApplication(BVAddOp(3), List(s0.sym, BitVectorLit(1, 3)))))
    val b0 = sys.bad.head
    b0 should be (OperatorApplication(EqualityOp, List(s0.sym, BitVectorLit(7, 3))))
  }

  // this example if from the official btor2tools repository
  "factorial4even" should "be parsed correctly" in {
    val fact =
      """
        |1 sort bitvec 4
        |2 one 1
        |3 state 1 factorial
        |4 state 1 i
        |5 init 1 3 2
        |6 init 1 4 2
        |7 add 1 4 2
        |8 mul 1 3 4
        |9 next 1 4 7
        |10 next 1 3 8
        |11 ones 1
        |12 sort bitvec 1
        |13 eq 12 4 11
        |14 bad 13
        |15 slice 12 3 0 0
        |16 constd 1 3
        |17 ugt 12 4 16
        |18 and 12 17 15
        |19 bad 18
        |""".stripMargin.split("\n")

    val sys = parse(fact)
    val factorial = sys.states.find(_.sym.id == "factorial").get
    val i = sys.states.find(_.sym.id == "i").get

    factorial.sym.id should be ("factorial")
    factorial.init should be (Some(BitVectorLit(1, 4)))
    factorial.next should be (Some(OperatorApplication(BVMulOp(4), List(factorial.sym, i.sym))))

    i.sym.id should be ("i")
    i.init should be (factorial.init)
    i.next should be (Some(OperatorApplication(BVAddOp(4), List(i.sym, BitVectorLit(1, 4)))))

    val b0 = sys.bad.head
    b0 should be (OperatorApplication(EqualityOp, List(i.sym, BitVectorLit(15, 4))))

    val b1 = sys.bad(1)
    val ugt = OperatorApplication(BVGTUOp(4), List(i.sym, BitVectorLit(3, 4)))
    val slice = OperatorApplication(BVExtractOp(0, 0), List(factorial.sym))
    val slice_b = OperatorApplication(EqualityOp, List(slice, BitVectorLit(1, 1)))
    // this is an artifact from the parse, serialize, parse
    val slice_b_artifact = OperatorApplication(EqualityOp, List(slice_b, BooleanLit(true)))
    b1 should be (OperatorApplication(ConjunctionOp, List(ugt, slice_b_artifact)))
  }

  // this example was written by Kevin Laeufer to demonstrate a bug in cosa2's parsing
  "const_array_example" should "be parsed correctly" in {
    val ca =
      """
        |1 sort bitvec 1
        |5 sort bitvec 5
        |23 sort bitvec 32
        |
        |; Symbolic Constant: addr
        |121 state 5 addr
        |122 next 5 121 121
        |
        |; Symbolic Constant: data
        |123 state 23 data
        |124 next 23 123 123
        |
        |; Symbolic Constant: mem
        |125 sort array 5 23
        |126 state 125 mem
        |127 next 125 126 126
        |
        |; mem[addr := data]
        |148 write 125 126 121 123
        |
        |; mem_n = mem[addr := data]
        |155 state 125 mem_n
        |156 init 125 155 148
        |157 next 125 155 155
        |
        |; bad: mem_n[a] != mem[a]
        |
        |; Symbolic Constant: a
        |200 state 5 a
        |201 next 5 200 200
        |
        |210 read 23 126 200
        |211 read 23 155 200
        |212 neq 1 210 211
        |213 bad 212
        |""".stripMargin.split("\n")

    val sys = parse(ca)
    val addr = sys.states.find(_.sym.id == "addr").get
    val data = sys.states.find(_.sym.id == "data").get
    val mem = sys.states.find(_.sym.id == "mem").get
    val mem_n = sys.states.find(_.sym.id == "mem_n").get
    val a = sys.states.find(_.sym.id == "a").get
    val b0 = sys.bad.head

    addr.next should be (Some(addr.sym))
    data.next should be (Some(data.sym))
    mem.next should be (Some(mem.sym))
    mem_n.next should be (Some(mem_n.sym))

    addr.sym.typ should be (BitVectorType(5))
    data.sym.typ should be (BitVectorType(32))
    mem.sym.typ should be (ArrayType(List(addr.sym.typ), data.sym.typ))

    mem_n.init should be (Some(ArrayStoreOperation(mem.sym, List(addr.sym), data.sym)))
    val mem_a = ArraySelectOperation(mem.sym, List(a.sym))
    val mem_n_a = ArraySelectOperation(mem_n.sym, List(a.sym))
    b0 should be (OperatorApplication(InequalityOp, List(mem_a, mem_n_a)))
  }

  // this was generated from the verilog source files for one of the benchmarks from the HWMCC'19
  val circular_pointer_src =
    """
      |; BTOR description generated by Yosys 0.9+932 (git sha1 2ed2e9c3, clang 8.0.0 -fPIC -Os) for module circular_pointer_fifo.
      |  ; begin inputs
      |    1 sort bitvec 1
      |    2 input 1 clk
      |    ; 2 \clk
      |    3 sort bitvec 32
      |    4 input 3 data_in
      |    ; 4 \data_in
      |    5 input 1 pop
      |    ; 5 \pop
      |    6 input 1 push
      |    ; 6 \push
      |    7 input 1 rst
      |    ; 7 \rst
      |  ; end inputs
      |  ; begin output data_out
      |      ; begin entries
      |        8 sort bitvec 7
      |        9 sort array 8 3
      |        10 state 9 entries
      |          ; begin $techmap\ff_wrPtr.$procdff$62
      |            11 sort bitvec 8
      |            12 state 11 ff_wrPtr.Q
      |            ; 12 \ff_wrPtr.Q
      |          ; end $techmap\ff_wrPtr.$procdff$62
      |        13 slice 8 12 6 0
      |        14 read 3 10 13
      |        ; 14 $memrd$\entries$tacas2020/circular_pointer_fifo_fixed.v:70$45_DATA
      |          ; begin $techmap\ff_rdPtr.$procdff$62
      |            15 state 11 ff_rdPtr.Q
      |            ; 15 \ff_rdPtr.Q
      |          ; end $techmap\ff_rdPtr.$procdff$62
      |        16 slice 8 15 6 0
      |        17 read 3 10 16
      |        ; 17 \data_out
      |      ; end entries
      |;     18 output 17 data_out
      |  ; end output data_out
      |  ; begin output empty
      |      ; begin $eq$tacas2020/circular_pointer_fifo_fixed.v:61$43
      |          ; begin $procdff$66
      |            19 state 11 cnt
      |            ; 19 \cnt
      |          ; end $procdff$66
      |        20 redor 1 19
      |        21 not 1 20
      |        ; 21 \empty
      |      ; end $eq$tacas2020/circular_pointer_fifo_fixed.v:61$43
      |;     22 output 21 empty
      |  ; end output empty
      |  ; begin output full
      |      ; begin $eq$tacas2020/circular_pointer_fifo_fixed.v:62$44
      |        23 const 11 10000000
      |        24 eq 1 19 23
      |        ; 24 \full
      |      ; end $eq$tacas2020/circular_pointer_fifo_fixed.v:62$44
      |;     25 output 24 full
      |  ; end output full
      |  ; begin wire ff_rdPtr.rst
      |    26 uext 1 7 0 ff_rdPtr.rst
      |  ; end wire ff_rdPtr.rst
      |  ; begin wire ff_rdPtr.en
      |      ; begin $or$tacas2020/circular_pointer_fifo_fixed.v:18$29
      |          ; begin $or$tacas2020/circular_pointer_fifo_fixed.v:18$28
      |            27 or 1 6 5
      |            ; 27 $or$tacas2020/circular_pointer_fifo_fixed.v:18$28_Y
      |          ; end $or$tacas2020/circular_pointer_fifo_fixed.v:18$28
      |        28 or 1 27 7
      |        ; 28 \clkEn
      |      ; end $or$tacas2020/circular_pointer_fifo_fixed.v:18$29
      |    29 uext 1 28 0 ff_rdPtr.en
      |  ; end wire ff_rdPtr.en
      |  ; begin wire ff_rdPtr.clk
      |    30 uext 1 2 0 ff_rdPtr.clk
      |  ; end wire ff_rdPtr.clk
      |  ; begin wire ff_rdPtr.Q
      |      ; begin wire ff_rdPtr.D
      |          ; begin $ternary$tacas2020/circular_pointer_fifo_fixed.v:52$42
      |              ; begin $ternary$tacas2020/circular_pointer_fifo_fixed.v:52$40
      |                  ; begin $add$tacas2020/circular_pointer_fifo_fixed.v:52$39
      |                    31 const 1 1
      |                    32 uext 11 31 7
      |                    33 add 11 15 32
      |                    ; 33 $add$tacas2020/circular_pointer_fifo_fixed.v:52$39_Y
      |                  ; end $add$tacas2020/circular_pointer_fifo_fixed.v:52$39
      |                34 const 11 00000000
      |                  ; begin $eq$tacas2020/circular_pointer_fifo_fixed.v:52$38
      |                    35 const 8 1111111
      |                    36 uext 11 35 1
      |                    37 eq 1 15 36
      |                    ; 37 $eq$tacas2020/circular_pointer_fifo_fixed.v:52$38_Y
      |                  ; end $eq$tacas2020/circular_pointer_fifo_fixed.v:52$38
      |                38 ite 11 37 34 33
      |                ; 38 $ternary$tacas2020/circular_pointer_fifo_fixed.v:52$40_Y [7:0]
      |              ; end $ternary$tacas2020/circular_pointer_fifo_fixed.v:52$40
      |            39 ite 11 5 38 15
      |            ; 39 \rdPtrNxt
      |          ; end $ternary$tacas2020/circular_pointer_fifo_fixed.v:52$42
      |        40 uext 11 39 0 ff_rdPtr.D
      |      ; end wire ff_rdPtr.D
      |      ; begin wire ff_wrPtr.rst
      |        41 uext 1 7 0 ff_wrPtr.rst
      |      ; end wire ff_wrPtr.rst
      |      ; begin wire ff_wrPtr.en
      |        42 uext 1 28 0 ff_wrPtr.en
      |      ; end wire ff_wrPtr.en
      |      ; begin wire ff_wrPtr.clk
      |        43 uext 1 2 0 ff_wrPtr.clk
      |      ; end wire ff_wrPtr.clk
      |      ; begin wire ff_wrPtr.Q
      |          ; begin wire ff_wrPtr.D
      |              ; begin $ternary$tacas2020/circular_pointer_fifo_fixed.v:35$37
      |                  ; begin $ternary$tacas2020/circular_pointer_fifo_fixed.v:35$35
      |                      ; begin $add$tacas2020/circular_pointer_fifo_fixed.v:35$34
      |                        44 uext 11 31 7
      |                        45 add 11 12 44
      |                        ; 45 $add$tacas2020/circular_pointer_fifo_fixed.v:35$34_Y
      |                      ; end $add$tacas2020/circular_pointer_fifo_fixed.v:35$34
      |                      ; begin $eq$tacas2020/circular_pointer_fifo_fixed.v:35$33
      |                        46 uext 11 35 1
      |                        47 eq 1 12 46
      |                        ; 47 $eq$tacas2020/circular_pointer_fifo_fixed.v:35$33_Y
      |                      ; end $eq$tacas2020/circular_pointer_fifo_fixed.v:35$33
      |                    48 ite 11 47 34 45
      |                    ; 48 $auto$wreduce.cc:454:run$69 [7:0]
      |                  ; end $ternary$tacas2020/circular_pointer_fifo_fixed.v:35$35
      |                49 ite 11 6 48 12
      |                ; 49 \wrPtrNxt
      |              ; end $ternary$tacas2020/circular_pointer_fifo_fixed.v:35$37
      |            50 uext 11 49 0 ff_wrPtr.D
      |          ; end wire ff_wrPtr.D
      |          ; begin wire clkEn
      |            51 uext 1 28 0 clkEn
      |          ; end wire clkEn
      |          ; begin wire cnt
      |              ; begin wire input_data
      |                  ; begin $ternary$tacas2020/circular_pointer_fifo_fixed.v:70$46
      |                    52 ite 3 6 4 14
      |                    ; 52 \input_data
      |                  ; end $ternary$tacas2020/circular_pointer_fifo_fixed.v:70$46
      |                53 uext 3 52 0 input_data
      |              ; end wire input_data
      |              ; begin wire rdPtr
      |                54 uext 11 15 0 rdPtr
      |              ; end wire rdPtr
      |              ; begin wire rdPtrNxt
      |                55 uext 11 39 0 rdPtrNxt
      |              ; end wire rdPtrNxt
      |              ; begin wire wrPtr
      |                56 uext 11 12 0 wrPtr
      |              ; end wire wrPtr
      |              ; begin wire wrPtrNxt
      |                57 uext 11 49 0 wrPtrNxt
      |              ; end wire wrPtrNxt
      |              ; begin next $techmap\ff_wrPtr.$procdff$62
      |                  ; begin $techmap\ff_wrPtr.$procmux$57
      |                      ; begin $techmap\ff_wrPtr.$procmux$54
      |                        58 ite 11 28 49 12
      |                        ; 58 $techmap\ff_wrPtr.$procmux$54_Y
      |                      ; end $techmap\ff_wrPtr.$procmux$54
      |                    59 ite 11 7 34 58
      |                    ; 59 $techmap\ff_wrPtr.$0\Q[7:0]
      |                  ; end $techmap\ff_wrPtr.$procmux$57
      |                60 next 11 12 59
      |              ; end next $techmap\ff_wrPtr.$procdff$62
      |              ; begin next $techmap\ff_rdPtr.$procdff$62
      |                  ; begin $techmap\ff_rdPtr.$procmux$57
      |                      ; begin $techmap\ff_rdPtr.$procmux$54
      |                        61 ite 11 28 39 15
      |                        ; 61 $techmap\ff_rdPtr.$procmux$54_Y
      |                      ; end $techmap\ff_rdPtr.$procmux$54
      |                    62 ite 11 7 34 61
      |                    ; 62 $techmap\ff_rdPtr.$0\Q[7:0]
      |                  ; end $techmap\ff_rdPtr.$procmux$57
      |                63 next 11 15 62
      |              ; end next $techmap\ff_rdPtr.$procdff$62
      |              ; begin next entries
      |                64 const 3 11111111111111111111111111111111
      |                65 read 3 10 13
      |                66 not 3 64
      |                67 and 3 65 66
      |                68 and 3 52 64
      |                69 or 3 68 67
      |                70 write 9 10 13 69
      |                71 redor 1 64
      |                72 ite 9 71 70 10
      |                73 next 9 10 72
      |              ; end next entries
      |              ; begin next $procdff$66
      |                  ; begin $procmux$60
      |                      ; begin $sub$tacas2020/circular_pointer_fifo_fixed.v:26$32
      |                          ; begin $add$tacas2020/circular_pointer_fifo_fixed.v:26$31
      |                            74 uext 11 6 7
      |                            75 add 11 19 74
      |                            ; 75 $add$tacas2020/circular_pointer_fifo_fixed.v:26$31_Y
      |                          ; end $add$tacas2020/circular_pointer_fifo_fixed.v:26$31
      |                        76 uext 11 5 7
      |                        77 sub 11 75 76
      |                        ; 77 $sub$tacas2020/circular_pointer_fifo_fixed.v:26$32_Y
      |                      ; end $sub$tacas2020/circular_pointer_fifo_fixed.v:26$32
      |                    78 ite 11 7 34 77
      |                    ; 78 $0\cnt[7:0]
      |                  ; end $procmux$60
      |                79 next 11 19 78
      |              ; end next $procdff$66
      |; end of yosys output
      |""".stripMargin
  "circular pointer fifo btor2 generated by yosys" should "parse" in {
    val sys = parse(circular_pointer_src.split("\n"))
  }

  // some properties and constraints that were generated by a custom script from Kevin Laeufer
  val custom_constraints =
    """
      |; Unroll for k=1 cycles
      |80 sort bitvec 16
      |81 const 80 0000000000000000
      |82 state 80 cycle_count
      |83 init 80 82 81
      |84 const 80 0000000000000001
      |85 add 80 82 84
      |86 next 80 82 85
      |; assert: (! (cycle_count = 2_16)) (b0)
      |87 const 80 0000000000000010
      |88 eq 1 82 87
      |89 not 1 88
      |90 not 1 89
      |91 bad 90
      |; Symbolic Constant: circular_pointer_fifo.mem
      |92 sort array 8 3
      |93 state 92 circular_pointer_fifo.mem
      |94 next 92 93 93
      |; Symbolic Constant: circular_pointer_fifo.count
      |95 state 11 circular_pointer_fifo.count
      |96 next 11 95 95
      |; Symbolic Constant: circular_pointer_fifo.read
      |97 state 8 circular_pointer_fifo.read
      |98 next 8 97 97
      |; Symbolic Constant: circular_pointer_fifo.Push.push_data
      |99 state 3 circular_pointer_fifo.Push.push_data
      |100 next 3 99 99
      |; Symbolic Constant: circular_pointer_fifo.PushPop.in
      |101 state 3 circular_pointer_fifo.PushPop.in
      |102 next 3 101 101
      |; Symbolic Constant: circular_pointer_fifo.edge@0
      |103 state 1 circular_pointer_fifo.edge@0
      |104 next 1 103 103
      |; Symbolic Constant: circular_pointer_fifo.edge@0_0
      |105 state 1 circular_pointer_fifo.edge@0_0
      |106 next 1 105 105
      |; Symbolic Constant: circular_pointer_fifo.edge@0_1
      |107 state 1 circular_pointer_fifo.edge@0_1
      |108 next 1 107 107
      |; Symbolic Constant: circular_pointer_fifo.edge@0_2
      |109 state 1 circular_pointer_fifo.edge@0_2
      |110 next 1 109 109
      |; Function: circular_pointer_fifo.Idle.mem_n = circular_pointer_fifo.mem
      |111 state 92 circular_pointer_fifo.Idle.mem_n
      |112 init 92 111 93
      |113 next 92 111 111
      |114 input 92 __watch_circular_pointer_fifo.Idle.mem_n
      |; assume: (__watch_circular_pointer_fifo.Idle.mem_n = circular_pointer_fifo.mem)
      |115 eq 1 114 93
      |116 constraint 115
      |; Function: circular_pointer_fifo.Idle.count_n = circular_pointer_fifo.count
      |117 state 11 circular_pointer_fifo.Idle.count_n
      |118 init 11 117 95
      |119 next 11 117 117
      |120 input 11 __watch_circular_pointer_fifo.Idle.count_n
      |; assume: (__watch_circular_pointer_fifo.Idle.count_n = circular_pointer_fifo.count)
      |121 eq 1 120 95
      |122 constraint 121
      |; Function: circular_pointer_fifo.Idle.read_n = circular_pointer_fifo.read
      |123 state 8 circular_pointer_fifo.Idle.read_n
      |124 init 8 123 97
      |125 next 8 123 123
      |126 input 8 __watch_circular_pointer_fifo.Idle.read_n
      |; assume: (__watch_circular_pointer_fifo.Idle.read_n = circular_pointer_fifo.read)
      |127 eq 1 126 97
      |128 constraint 127
      |; Function: circular_pointer_fifo.Push.mem_n = circular_pointer_fifo.mem[(circular_pointer_fifo.read + circular_pointer_fifo.count[0:6]) := circular_pointer_fifo.Push.push_data]
      |129 slice 8 95 6 0
      |130 add 8 97 129
      |131 write 92 93 130 99
      |132 state 92 circular_pointer_fifo.Push.mem_n
      |133 init 92 132 131
      |134 next 92 132 132
      |135 input 92 __watch_circular_pointer_fifo.Push.mem_n
      |; assume: (__watch_circular_pointer_fifo.Push.mem_n = circular_pointer_fifo.mem[(circular_pointer_fifo.read + circular_pointer_fifo.count[0:6]) := circular_pointer_fifo.Push.push_data])
      |136 eq 1 135 131
      |137 constraint 136
      |; Function: circular_pointer_fifo.Push.count_n = (circular_pointer_fifo.count + 1_8)
      |138 const 11 00000001
      |139 add 11 95 138
      |140 state 11 circular_pointer_fifo.Push.count_n
      |141 init 11 140 139
      |142 next 11 140 140
      |143 input 11 __watch_circular_pointer_fifo.Push.count_n
      |; assume: (__watch_circular_pointer_fifo.Push.count_n = (circular_pointer_fifo.count + 1_8))
      |144 eq 1 143 139
      |145 constraint 144
      |; Function: circular_pointer_fifo.Push.read_n = circular_pointer_fifo.read
      |146 state 8 circular_pointer_fifo.Push.read_n
      |147 init 8 146 97
      |148 next 8 146 146
      |149 input 8 __watch_circular_pointer_fifo.Push.read_n
      |; assume: (__watch_circular_pointer_fifo.Push.read_n = circular_pointer_fifo.read)
      |150 eq 1 149 97
      |151 constraint 150
      |; Function: circular_pointer_fifo.Pop.pop_data = circular_pointer_fifo.mem[circular_pointer_fifo.read]
      |152 read 3 93 97
      |153 state 3 circular_pointer_fifo.Pop.pop_data
      |154 init 3 153 152
      |155 next 3 153 153
      |156 input 3 __watch_circular_pointer_fifo.Pop.pop_data
      |; assume: (__watch_circular_pointer_fifo.Pop.pop_data = circular_pointer_fifo.mem[circular_pointer_fifo.read])
      |157 eq 1 156 152
      |158 constraint 157
      |; Function: circular_pointer_fifo.Pop.mem_n = circular_pointer_fifo.mem
      |159 state 92 circular_pointer_fifo.Pop.mem_n
      |160 init 92 159 93
      |161 next 92 159 159
      |162 input 92 __watch_circular_pointer_fifo.Pop.mem_n
      |; assume: (__watch_circular_pointer_fifo.Pop.mem_n = circular_pointer_fifo.mem)
      |163 eq 1 162 93
      |164 constraint 163
      |; Function: circular_pointer_fifo.Pop.count_n = (circular_pointer_fifo.count - 1_8)
      |165 sub 11 95 138
      |166 state 11 circular_pointer_fifo.Pop.count_n
      |167 init 11 166 165
      |168 next 11 166 166
      |169 input 11 __watch_circular_pointer_fifo.Pop.count_n
      |; assume: (__watch_circular_pointer_fifo.Pop.count_n = (circular_pointer_fifo.count - 1_8))
      |170 eq 1 169 165
      |171 constraint 170
      |; Function: circular_pointer_fifo.Pop.read_n = (circular_pointer_fifo.read + 1_7)
      |172 const 8 0000001
      |173 add 8 97 172
      |174 state 8 circular_pointer_fifo.Pop.read_n
      |175 init 8 174 173
      |176 next 8 174 174
      |177 input 8 __watch_circular_pointer_fifo.Pop.read_n
      |; assume: (__watch_circular_pointer_fifo.Pop.read_n = (circular_pointer_fifo.read + 1_7))
      |178 eq 1 177 173
      |179 constraint 178
      |; Function: circular_pointer_fifo.PushPop.out = ((circular_pointer_fifo.count = 0_8) ? circular_pointer_fifo.PushPop.in : circular_pointer_fifo.mem[circular_pointer_fifo.read])
      |180 const 11 00000000
      |181 eq 1 95 180
      |182 ite 3 181 101 152
      |183 state 3 circular_pointer_fifo.PushPop.out
      |184 init 3 183 182
      |185 next 3 183 183
      |186 input 3 __watch_circular_pointer_fifo.PushPop.out
      |; assume: (__watch_circular_pointer_fifo.PushPop.out = ((circular_pointer_fifo.count = 0_8) ? circular_pointer_fifo.PushPop.in : circular_pointer_fifo.mem[circular_pointer_fifo.read]))
      |187 eq 1 186 182
      |188 constraint 187
      |; Function: circular_pointer_fifo.PushPop.mem_n = circular_pointer_fifo.mem[(circular_pointer_fifo.read + circular_pointer_fifo.count[0:6]) := circular_pointer_fifo.PushPop.in]
      |189 write 92 93 130 101
      |190 state 92 circular_pointer_fifo.PushPop.mem_n
      |191 init 92 190 189
      |192 next 92 190 190
      |193 input 92 __watch_circular_pointer_fifo.PushPop.mem_n
      |; assume: (__watch_circular_pointer_fifo.PushPop.mem_n = circular_pointer_fifo.mem[(circular_pointer_fifo.read + circular_pointer_fifo.count[0:6]) := circular_pointer_fifo.PushPop.in])
      |194 eq 1 193 189
      |195 constraint 194
      |; Function: circular_pointer_fifo.PushPop.count_n = circular_pointer_fifo.count
      |196 state 11 circular_pointer_fifo.PushPop.count_n
      |197 init 11 196 95
      |198 next 11 196 196
      |199 input 11 __watch_circular_pointer_fifo.PushPop.count_n
      |; assume: (__watch_circular_pointer_fifo.PushPop.count_n = circular_pointer_fifo.count)
      |200 eq 1 199 95
      |201 constraint 200
      |; Function: circular_pointer_fifo.PushPop.read_n = (circular_pointer_fifo.read + 1_7)
      |202 state 8 circular_pointer_fifo.PushPop.read_n
      |203 init 8 202 173
      |204 next 8 202 202
      |205 input 8 __watch_circular_pointer_fifo.PushPop.read_n
      |; assume: (__watch_circular_pointer_fifo.PushPop.read_n = (circular_pointer_fifo.read + 1_7))
      |206 eq 1 205 173
      |207 constraint 206
      |; -------------------
      |; - Transition 0 -> 1
      |; -------------------
      |; assume: ((cycle_count = 0_16) -> (cnt u< 129_8))
      |208 const 11 10000001
      |209 ult 1 19 208
      |210 eq 1 82 81
      |211 implies 1 210 209
      |212 constraint 211
      |; assume: ((cycle_count = 0_16) -> (ff_rdPtr.Q u< 128_8))
      |213 const 11 10000000
      |214 ult 1 15 213
      |215 implies 1 210 214
      |216 constraint 215
      |; assume: ((cycle_count = 0_16) -> (ff_wrPtr.Q u< 128_8))
      |217 ult 1 12 213
      |218 implies 1 210 217
      |219 constraint 218
      |; assume: ((cycle_count = 0_16) -> ((cnt = 0_8) ? (ff_rdPtr.Q = ff_wrPtr.Q) : (cnt = ((... u< ...) ? (... - ...) : (... + ...)))))
      |220 sub 11 12 15
      |221 add 11 213 220
      |222 ult 1 15 12
      |223 ite 11 222 220 221
      |224 eq 1 19 223
      |225 eq 1 15 12
      |226 eq 1 19 180
      |227 ite 1 226 225 224
      |228 implies 1 210 227
      |229 constraint 228
      |; assume: ((cycle_count = 0_16) -> (True -> (circular_pointer_fifo.count = cnt)))
      |230 eq 1 95 19
      |231 one 1
      |232 implies 1 231 230
      |233 implies 1 210 232
      |234 constraint 233
      |""".stripMargin
  "custom constraints" should "parse" in {
    val sys = parse((circular_pointer_src ++ custom_constraints).split("\n"))
  }
}
