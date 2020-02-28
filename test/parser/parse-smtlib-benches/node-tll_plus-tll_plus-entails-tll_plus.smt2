(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node ((node (left Loc) (right Loc) (parent Loc) (next Loc))))

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

(declare-const a Loc)
(declare-const c Loc)

(assert (exists ((l Loc) (r Loc) (z Loc))
            (sep (pto a (node l r (as nil Loc) (as nil Loc)))
                 (tll_plus l a c z)
                 (tll_plus r a z (as nil Loc)))
        )
)
(assert (not (tll_plus a (as nil Loc) c (as nil Loc))))

(check-sat)