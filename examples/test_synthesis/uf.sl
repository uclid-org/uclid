(declare-var uf (-> (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))

(synth-fun foo ((x (BitVec 32))
                (y (BitVec 32))) (BitVec 32))

(declare-var x (BitVec 32))
(declare-var y (BitVec 32))

(constraint (or (= (foo x y) (uf x y))(= (foo x y) 10)))

(check-synth)
