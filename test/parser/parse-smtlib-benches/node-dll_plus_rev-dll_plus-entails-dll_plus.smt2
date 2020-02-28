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

(declare-const a Loc)
(declare-const c Loc)

(assert (exists ((x Loc) (n Loc) (b Loc))
            (sep (pto x (node n b))
                 (dllseg_plus_rev a (as nil Loc) b (as nil Loc))
                 (dllseg_plus n x c (as nil Loc)))
        )
)
(assert (not (dllseg_plus_rev a (as nil Loc) c (as nil Loc))))

(check-sat)