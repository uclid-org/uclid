(set-logic SEPLOGLIA)

(declare-datatype Node ((empty) (node_cons (data Int) (ref Int))))

(define-fun q ((x Int) (a Int) (x1 Int) (y Int) (b Int) (y1 Int)) Bool 
    (and (sep (pto x (node_cons a x1)) (pto y (node_cons b y1))) (< a b))
)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const t Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and (sep (q x a y y b z) (pto z (node_cons c t))) 
             (sep (pto x (node_cons a y)) (q y b z z c t))
        )
)

(assert (not (sep (pto y (node_cons b z)) (q x a y z c t))))

(check-sat)