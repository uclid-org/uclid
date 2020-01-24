(set-logic BV)

(synth-inv inv-f ((x (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(define-fun pre-f ((x (BitVec 32))) Bool
    (= x #x0000000A)
)

(define-fun trans-f ((x (BitVec 32))(x! (BitVec 32))) Bool
    (and (bvuge x #x0000000A) (= x! (bvadd x #x00000002)))
)

(define-fun post-f ((x (BitVec 32))) Bool
    (or (= #x00000000 (bvurem x #x00000002))(bvuge x #x0000000A))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


