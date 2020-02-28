(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node ((node (left Loc) (right Loc)
                                            (parent Loc) (next Loc))))

(define-fun-rec tll_plus ((root Loc) (parent Loc) (ll Loc) (lr Loc)) Bool
    (or (and (pto root (node (as nil Loc) (as nil Loc) parent lr))
             (= root ll))
        (exists ((l Loc) (r Loc) (z Loc))
            (sep (pto root (node l r parent (as nil Loc)))
                 (tll_plus l root ll z)
                 (tll_plus r root z lr))
        )
    )
)

(define-fun-rec tll_aux ((x Loc) (p Loc) (z Loc)
                         (back Loc) (top Loc) (mright Loc)) Bool
    (or (exists ((up Loc) (r Loc) (lr Loc))
            (sep (pto x (node back r up (as nil Loc)))
                 (tll_aux up p lr x top mright)
                 (tll_plus r x z lr))
        )
        (exists ((r Loc))
            (and (= x top)
                 (sep (pto x (node back r p (as nil Loc)))
                       (tll_plus r x z mright))
            )
        )
    )
)

(define-fun-rec tll_plus_rev ((top Loc) (p Loc) (mleft Loc) (mright Loc)) Bool
    (or (and (pto top (node (as nil Loc) (as nil Loc) p mright))
             (= top mleft))
        (exists ((x Loc) (up Loc) (lr Loc))
            (and (= mleft x)
                 (sep (pto x (node (as nil Loc) (as nil Loc) up lr))
                      (tll_aux up p lr x top mright))
            )
        )
    )
)

(declare-const x Loc)
(declare-const y Loc)
(declare-const u Loc)
(declare-const v Loc)

(assert (tll_plus_rev x y u v))
(assert (not (tll_plus x y u v)))

(check-sat)