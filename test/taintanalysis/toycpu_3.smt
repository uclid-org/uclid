(set-option :fp.engine spacer)
(declare-datatypes ((_tuple_0 0)) (((_tuple_0 (__f1 (_ BitVec 2)) (__f2 (_ BitVec 2)) (__f3 (_ BitVec 2))))))
(declare-rel invHyper ((Array (_ BitVec 2) (_ BitVec 32)) (_ BitVec 2) (_ BitVec 2) (Array _tuple_0 Bool) (Array (_ BitVec 2) (_ BitVec 32)) (_ BitVec 2) (_ BitVec 2) (Array _tuple_0 Bool)))
(declare-rel error_next_hyp_assert_0 ())
(declare-var A (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var B (_ BitVec 2))
(declare-var C (_ BitVec 2))
(declare-var D (Array _tuple_0 Bool))
(declare-var E (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var F (_ BitVec 2))
(declare-var G (_ BitVec 2))
(declare-var H (Array _tuple_0 Bool))
(declare-var I (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var J (_ BitVec 2))
(declare-var K (_ BitVec 2))
(declare-var L (Array _tuple_0 Bool))
(declare-var M (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var N (_ BitVec 2))
(declare-var O (_ BitVec 2))
(declare-var P (Array _tuple_0 Bool))
(declare-var Q (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var R (_ BitVec 2))
(declare-var S (_ BitVec 2))
(declare-var T (Array _tuple_0 Bool))
(declare-var U (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var V (_ BitVec 2))
(declare-var W (_ BitVec 2))
(declare-var X (Array _tuple_0 Bool))
(declare-var A1 (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var B1 (_ BitVec 2))
(declare-var C1 (_ BitVec 2))
(declare-var D1 (Array _tuple_0 Bool))
(declare-var E1 (Array (_ BitVec 2) (_ BitVec 32)))
(declare-var F1 (_ BitVec 2))
(declare-var G1 (_ BitVec 2))
(declare-var H1 (Array _tuple_0 Bool))

(rule (! (let ((a!1 (forall ((a (_ BitVec 2)))
                   (! (or (not (select D
                                       (_tuple_0 a
                                                 C
                                                 B)))
                          (= (select A a)
                             (select E a)))
                      :skolemid _skolem_0
                      :qid _forall_0))))
        (=> (and true true a!1)
            (invHyper A
                      B
                      C
                      D
                      E
                      F
                      G
                      H)))
       :named initHyperRule))
(rule  (! (let ((a!1 (forall ((a (_ BitVec 2)))
                   (! (or (not (select T
                                       (_tuple_0 a
                                                 S
                                                 R)))
                          (= (select Q a)
                             (select U a)))
                      :skolemid _skolem_0
                      :qid _forall_0))))
        (=> (and (invHyper I
                           J
                           K
                           L
                           M
                           N
                           O
                           P)
                 (= R J)
                 (= T L)
                 (= Q I)
                 (= S K)
                 (= V N)
                 (= X P)
                 (= U M)
                 (= W O)
                 a!1)
            (invHyper Q
                      R
                      S
                      T
                      U
                      V
                      W
                      X)))
      :named nextHyperRule))
(rule 
   (! (let ((a!1 (forall ((a (_ BitVec 2)))
                   (! (or (not (select D1
                                       (_tuple_0 a
                                                 C1
                                                 B1)))
                          (= (select A1 a)
                             (select E1 a)))
                      :skolemid _skolem_0
                      :qid _forall_0))))
       (=> (and (invHyper A1
                           B1
                           C1
                           D1
                           E1
                           F1
                           G1
                           H1)
                 (not a!1))
           error_next_hyp_assert_0))
   :named next_hyp_assert_1))
(query error_next_hyp_assert_0 :print-certificate true)
