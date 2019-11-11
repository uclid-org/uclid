(set-logic BV)

(synth-inv inv-f ((x (BitVec 32))(y (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(declare-primed-var y (BitVec 32))

(define-fun pre-f ((x (BitVec 32))(y (BitVec 32))) Bool
    (= x #x00000000)
)

(define-fun trans-f ((x (BitVec 32))(y (BitVec 32))(x! (BitVec 32))(y! (BitVec 32))) Bool
    (or (and (= (bvurem y #x00000002) #x00000000) (and (= x! (bvadd x #x00000014)) (and (= y! y) (bvult x #x00000063)))) (and (= x! (bvsub #x00000005 x)) (and (= y! y) (bvult x #x00000063))))
)

(define-fun post-f ((x (BitVec 32))(y (BitVec 32))) Bool
    (or (= (bvurem x #x00000002) (bvurem y #x00000002))(bvult x #x00000063))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


