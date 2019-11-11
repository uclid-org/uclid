(set-logic BV)

(synth-inv inv-f ((x (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(define-fun pre-f ((x (BitVec 32))) Bool
    (= x #x0ffffff0)
)

(define-fun trans-f ((x (BitVec 32))(x! (BitVec 32))) Bool
    (and (bvugt x #x00000000) (= x! (bvsub x #x00000002)))
)

(define-fun post-f ((x (BitVec 32))) Bool
    (or (= #x00000000 (bvurem x #x00000002))(bvugt x #x00000000))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


