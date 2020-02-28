(set-logic SEPLOGLIA)

(define-fun p ((x Int) (a Int) (y Int) (b Int)) Bool 
    (and (sep (pto x a) (pto y b))
         (< a b)
    )
)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and (sep (p x a y b) (pto z c)) 
             (sep (pto x a) (p y b z c))
        )
)

(assert (not ((sep (pto y b) (p x a z c)))))

(check-sat)