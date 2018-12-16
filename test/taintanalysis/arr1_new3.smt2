(set-option :fixedpoint.engine spacer)

(declare-var a1 Int)
(declare-var a2 Int)
(declare-var b1 Int)
(declare-var b2 Int)
(declare-var d1 Int)
(declare-var d2 Int)
(declare-var temp Int)

(declare-var mem1 (Array Int Int))
(declare-var mem2 (Array Int Int))
(declare-var rng (Array Int Bool))
(declare-var initAssume1 Bool)
(declare-var initAssume2 Bool)
(declare-rel err2_1 ()) ; For hyperinvariant 2
(declare-rel err2_2 ()) ; For hyperinvariant 2

(declare-rel err1 ()) ; For hyperinvariant 1
(declare-var j Int)

; HyperAxioms
; (rule (= a1 a2)) encoded
; (rule (=> (not initAssume1) (=> (select rng a1) (= b1 b2))))
; (rule (=> initAssume1 (forall ((i Int)) (=> (select rng i) (= (select mem1 i) (select mem2 i))))))

;a1 b1 d1 initAssume1 mem1 rng, a2 b2 d2 initAssume2 mem2 rng 
(declare-rel inv (Int Int Int Bool (Array Int Int) (Array Int Bool) Int Int Int Bool (Array Int Int) (Array Int Bool)))

; Init 
(rule (=> (and (= d1 0) (= d2 0) (not initAssume1) (not initAssume2)
               (forall ((i Int)) (=> (select rng i) (= (select mem1 i) (select mem2 i)))))
          (inv a1 b1 d1 initAssume1 mem1 rng a2 b2 d2 initAssume2 mem2 rng)))

; Transition 
(rule (=> (and (= a1 a2) (=> (select rng a1) (= b1 b2))
          (inv a1 b1 d1 initAssume1 mem1 rng a2 b2 d2 initAssume2 mem2 rng)) 
          (inv a1 b1 (select mem1 a1) false (store mem1 a1 b1) rng a2 b2 (select mem2 a2) false (store mem2 a2 b2) rng)))

(rule (=> (and (inv a1 b1 d1 initAssume1 mem1 rng a2 b2 d2 initAssume2 mem2 rng) (select rng a1) (not (= d1 d2))) err1))
(query err1 :print-certificate true)

(rule (=> (and 
                (inv a1 b1 d1 initAssume1 mem1 rng a2 b2 d2 initAssume2 mem2 rng)
                (not (forall ((i Int)) (=> (select rng i) (= (select mem1 i) (select mem2 i)))))) err2_2))
(query err2_2 :print-certificate true) 
; (rule (=> (and (= a1 a2) (=> (not initAssume1) (=> (select rng a1) (= b1 b2)))
;                (=> initAssume1 (forall ((i Int)) (=> (select rng i) (= (select mem1 i) (select mem2 i)))))
;                (inv a1 b1 d1 initAssume1 mem1 rng a2 b2 d2 initAssume2 mem2 rng)
;                (and (select rng j) (not (= (select mem1 j) (select mem2 j))))) err2_1))
; (query err2_2 :print-answer true)
; (query err2_1 :print-answer true)  
; (query inv :print-certificate true)
