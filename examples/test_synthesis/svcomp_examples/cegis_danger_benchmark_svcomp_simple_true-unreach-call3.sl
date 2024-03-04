(set-logic BV)

(synth-inv inv-f ((x (BitVec 32))(N (BitVec 32)))
 )

(declare-primed-var x (BitVec 32))

(declare-primed-var N (BitVec 32))

(define-fun pre-f ((x (BitVec 32))(N (BitVec 32))) Bool
    (and (= x #x00000000) (= N (bvurem N #x0000FFFF)))
)

(define-fun trans-f ((x (BitVec 32))(N (BitVec 32))(x! (BitVec 32))(N! (BitVec 32))) Bool
    (and (bvult x N) (and (= x! (bvadd x #x00000002)) (= N! N)))
)

(define-fun post-f ((x (BitVec 32))(N (BitVec 32))) Bool
    (or (= #x00000000 (bvurem x #x00000002))(bvult x N))
)

(inv-constraint inv-f pre-f trans-f post-f) 
(check-synth)


