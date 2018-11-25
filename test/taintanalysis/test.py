from z3 import *

fp = Fixedpoint()
fp.set(engine='pdr')

# transition system
# var {
#   a : integer
#   at, bt, dt, mt1 : boolean
#   mt2 : [int]boolean
# }

# variables.
a, i = Ints('a i')
dt, mt1 = Bools('dt mt1')
mt2 = Array('mt2', IntSort(), BoolSort())
rng = Function('rng', IntSort(), BoolSort())

# relations
inv = Function('inv', BoolSort(), BoolSort(), ArraySort(IntSort(), BoolSort()), BoolSort())
err = Function('err', BoolSort())

eqT = (K(IntSort(), True))
# register them
fp.register_relation(inv)
fp.register_relation(err)

# init {
#   dt = true
#   mt1 = true
#   assume (forall (i : integer) :: rng(i) ==> mt2[i])
# }
# init encoding
init = And(dt, mt1)
fp.rule(inv(dt, mt1, eqT), init)

# next {
#   mt1' = true && mt1
#   mt2' = mt2[a -> rng(a)]
#   dt = mt1 && mt2[a]
# }
# transition encoding
mt1p = mt1
mt2p = Store(mt2, a, rng(a))
dtp = And(mt1, mt2[a])
fp.rule(inv(dtp, mt1p, mt2p), [inv(dt, mt1, mt2)])

# error
fp.rule(err(), [inv(dt, mt1, mt2), Not(dt)])

print (fp)
print (fp.query(err))
