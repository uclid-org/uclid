(set-logic BV)

(synth-inv inv-f ((x (BitVec 32))(y (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(declare-primed-var y (BitVec 32))

(define-fun pre-f ((x (BitVec 32))(y (BitVec 32))) Bool
    (= x y)
)

(define-fun trans-f ((x (BitVec 32))(x! (BitVec 32))(y (BitVec 32))(y! (BitVec 32))) Bool
    (and (bvult x #x00000400) (and (= x! (bvadd x #x00000001)) (= y! (bvadd y #x00000001))))
)

(define-fun post-f ((x (BitVec 32))(y (BitVec 32))) Bool
    (or (= x y) (bvult x #x00000400))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


