(set-logic SEPLOGLIA)

(declare-const x Int)
(declare-const y Int)

(declare-const a Int)
(declare-const b Int)

(assert (and (pto x a) (pto y b)))

(assert (not (and (= x y) (= a b))))

(check-sat)