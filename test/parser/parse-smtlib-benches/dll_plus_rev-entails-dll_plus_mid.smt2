(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node ((node (next Loc) (prev Loc))))

(define-fun-rec dllseg_plus ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and (pto hd (node nx pr)) (= hd tl))
        (exists ((x Loc)) (sep (pto hd (node x pr)) (dllseg_plus x hd tl nx))))
)

(define-fun-rec dllseg_plus_rev ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and (pto hd (node nx pr)) (= hd tl))
        (exists ((x Loc)) (sep (pto tl (node nx x)) (dllseg_plus_rev hd pr x tl)))
    )
)

(define-fun-rec dllseg_plus_mid ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and (pto hd (node nx pr)) (= hd tl))
        (or (sep (pto hd (node tl pr)) (pto tl (node nx hd)))
            (exists ((x Loc) (y Loc) (z Loc))
                (sep (pto x (node y z)) (dllseg_plus y x tl nx) (dllseg_plus_rev hd pr z nx))
            )
        )
    )
)

(declare-const x Loc)
(declare-const y Loc)

(assert (dllseg_plus_rev x (as nil Loc) y (as nil Loc)))
(assert (not (dllseg_plus_mid x (as nil Loc) y (as nil Loc))))

(check-sat)