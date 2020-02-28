(set-logic SEPLOG)

(declare-sort Loc 0)

(declare-datatype Node1 ((node1 (next Loc) (prev Loc))))

(declare-datatype Node2 ((node2 (next Loc) (prev Loc) (down Loc))))

(define-fun-rec dll1_plus ((hd Loc) (pr Loc)) Bool
    (or (pto hd (node1 (as nil Loc) pr))
        (exists ((x Loc)) (sep (pto hd (node1 x pr)) (dll1_plus x hd))))
)

(define-fun-rec dllseg2_plus ((hd Loc) (pr Loc)
                              (tl Loc) (nx Loc)) Bool
    (or (exists ((down_hd Loc))
            (and (= hd tl)
                 (sep (pto hd (node2 nx pr down_hd))
                      (dll1_plus down_hd (as nil Loc)))))
        (exists ((x Loc) (down_hd Loc))
            (sep (pto hd (node2 x pr down_hd))
                 (dll1_plus down_hd (as nil Loc))
                 (dllseg2_plus x hd tl nx))))
)

(define-fun-rec dllseg2_plus_rev ((hd Loc) (pr Loc)
                                  (tl Loc) (nx Loc)) Bool
    (or (exists ((down_hd Loc))
            (and (= hd tl)
                 (sep (pto hd (node2 nx pr down_hd))
                      (dll1_plus down_hd (as nil Loc)))))
        (exists ((x Loc) (down_hd Loc))
            (sep (pto tl (node2 nx x down_hd))
                 (dll1_plus down_hd (as nil Loc))
                 (dllseg2_plus_rev hd pr x tl))))
)

(declare-const x Loc)
(declare-const y Loc)
(declare-const u Loc)
(declare-const v Loc)

(assert (dllseg2_plus x y u v))
(assert (not (dllseg2_plus_rev x y u v)))

(check-sat)