(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node ((node (left Loc) (right Loc) (parent Loc))))

(define-fun-rec tpp_plus ((x Loc) (back Loc)) Bool
    (or (pto x (node (as nil Loc) (as nil Loc) back))
        (exists ((y Loc) (z Loc))
            (sep (pto x (node y z back))
                 (tpp_plus y x)
                 (tpp_plus z x))
        )
    )
)

(define-fun-rec tpp_aux ((x Loc) (down Loc) (top Loc) (b Loc)) Bool
    (or (exists ((up Loc) (right Loc))
            (sep (pto x (node down right up))
                 (tpp_plus right x)
                 (tpp_aux up x top b))
        )
        (exists ((up Loc) (left Loc))
            (sep (pto x (node left down up))
                 (tpp_plus left x)
                 (tpp_aux up x top b))
        )
        (exists ((right Loc))
            (and (= x top)
                 (sep (pto x (node down right b))
                       (tpp_plus right x))
            )
        )
        (exists ((left Loc))
            (and (= x top)
                 (sep (pto x (node left down b))
                       (tpp_plus left x))
            )
        )
    )
)

(define-fun-rec tpp_plus_rev ((top Loc) (b Loc)) Bool
    (or (pto top (node (as nil Loc) (as nil Loc) b))
        (exists ((x Loc) (up Loc))
            (sep (pto x (node (as nil Loc) (as nil Loc) up))
                 (tpp_aux up x top b))
        )
    )
)

(declare-const x Loc)
(declare-const y Loc)

(assert (tpp_plus x y))
(assert (not (tpp_plus_rev x y)))

(check-sat)