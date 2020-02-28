(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node ((node (next Loc) (prev Loc))))

(define-fun-rec dllseg_plus ((hd Loc) (pr Loc) (tl Loc) (nx Loc)) Bool
    (or (and (pto hd (node nx pr)) (= hd tl))
        (exists ((x Loc)) (sep (pto hd (node x pr)) (dllseg_plus x hd tl nx))))
)

(declare-const x Loc)
(declare-const c Loc)

(assert (exists ((y Loc) (a Loc))
            (sep (pto x (node y (as nil Loc)))
                 (pto y (node a x))
                 (dllseg_plus a y c (as nil Loc)))
        )
)
(assert (not (dllseg_plus x (as nil Loc) c (as nil Loc))))

(check-sat)