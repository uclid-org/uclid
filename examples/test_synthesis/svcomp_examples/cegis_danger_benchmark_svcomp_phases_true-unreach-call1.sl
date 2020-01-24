(set-logic BV)

(synth-inv inv-f ((x (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(define-fun pre-f ((x (BitVec 32))) Bool
    (= x #x00000000)
)

(define-fun trans-f ((x (BitVec 32))(x! (BitVec 32))) Bool
    (and (bvult x #x0fffffff) (or (and (bvult x #x0000fff0) (= x! (bvadd x #x00000001))) (= x! (bvadd x #x00000002))))
)

(define-fun post-f ((x (BitVec 32))) Bool
    (or (= #x00000000 (bvurem x #x00000002))(bvult x #x0fffffff))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


