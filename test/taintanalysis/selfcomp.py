import z3
import itertools

class TransitionSystem(object):
    def variables(self, suffix = ''):
        if suffix != '':
            s = '_' + suffix
        else:
            s = ''
        return [z3.Int('x' + s), z3.Int('y' + s)]

    def sorts(self):
        return [z3.IntSort(), z3.IntSort()]

    def init(self, xs):
        "Init(x, y) = (x == 0 && y == 1)"
        return [xs[0] == 0, xs[1] == 1]

    def tr(self, xs, xsp):
        "Tr(x, y, x', y') = (x' == x + 1 && y' == x + y)"
        return [xsp[0] == xs[0] + 1,
                xsp[1] == xs[0] + xs[1]]

class SelfComposedTransitionSystem(object):
    def __init__(self, M):
        self.M = M
    def variables(self, suffix = ''):
        v1 = self.M.variables('_1' + suffix)
        v2 = self.M.variables('_2' + suffix)
        return v1 + v2
    def sorts(self):
        return self.M.sorts() + self.M.sorts()
    def init(self, xs):
        m = len(xs) // 2
        xs1 = xs[:m]
        xs2 = xs[m:]
        return self.M.init(xs1) + self.M.init(xs2)
    def tr(self, xs, xsp):
        m = len(xs) // 2
        xs1  = xs[:m]
        xs2  = xs[m:]
        xsp1 = xsp[:m]
        xsp2 = xsp[m:]
        return self.M.tr(xs1, xsp1) + self.M.tr(xs2, xsp2)

def relationalInduction(M, Msc, bad_sc):
    xs = Msc.variables()
    xsp = Msc.variables('prime')

    bad = z3.simplify(z3.And(bad_sc(xs)))
    init = z3.And(Msc.init(xs))
    check = z3.simplify(z3.And(init, bad))

    S = z3.Solver()
    S.push()
    S.add(check)
    rInit = (S.check())
    S.pop()
    assert (rInit == z3.unsat)

    S.push()
    good_assume = z3.simplify(z3.And(z3.Not(bad_sc(xs))))
    bad_proofob = z3.simplify(z3.And(bad_sc(xsp)))
    trx = z3.simplify(z3.And(Msc.tr(xs, xsp)))
    S.add(good_assume)
    S.add(bad_proofob)
    S.add(trx)
    n = len(xs) // 2
    while S.check() == z3.sat:
        m = S.model()
        xm1 = [m.eval(xsi) for xsi in xs[:n]]
        xm2 = [m.eval(xsi) for xsi in xs[n:]]
        bad1 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm1, xs)])]
        bad2 = lambda xs: [z3.And(*[xi == xmi for (xi, xmi) in itertools.izip(xm2, xs)])]
        print (xm1, xm2)
        (r1, vs1, inv1) = fixedpoint(M, bad1)
        if r1 == z3.unsat:
            sub1 = zip(vs1, xs[:n])
            sub2 = zip(vs1, xs[n:])
            p1 = z3.substitute(inv1, *sub1)
            p2 = z3.substitute(inv1, *sub2)
            S.add(p1)
            S.add(p2)
            print (p1, p2)
            continue
        (r2, vs2, inv2) = fixedpoint(M, bad2)
        if r2 == z3.unsat:
            sub1 = zip(vs2, xs[:n])
            sub2 = zip(vs2, xs[n:])
            p1 = z3.substitute(inv2, *sub1)
            p2 = z3.substitute(inv2, *sub2)
            S.add(p1)
            S.add(p2)
            print (p1, p2)
    S.pop()
    
def fixedpoint(M, bad):
    fp = z3.Fixedpoint()
    options = {'engine':'spacer'}
    fp.set(**options)

    xs = M.variables()
    xsp = M.variables('prime')
    sorts = M.sorts() + [z3.BoolSort()]
    inv = z3.Function('inv', *sorts)
    err = z3.Function('err', z3.BoolSort())

    fp.register_relation(inv)
    fp.register_relation(err)
    for zi in xs + xsp:
        fp.declare_var(zi)

    inv_xs = inv(*xs)
    inv_xsp = inv(*xsp)
    fp.rule(inv_xs, M.init(xs))
    fp.rule(inv_xsp, M.tr(xs, xsp) + [inv_xs])
    fp.rule(err(), bad(xs) + [inv_xs])

    if fp.query(err) == z3.unsat:
        inv = fp.get_answer()
        print("INV:: ", inv)
        assert inv.is_forall()
        body = inv.body()
        assert z3.is_eq(body)
        print("BODY:: ", body)
        fapp = body.arg(0)
        print("FAPP:: ", fapp)
        assert (z3.is_app(fapp))
        args = [fapp.arg(i) for i in range(body.num_args())]
        print("ARGS:: ", args)
        assert len(args) == len(xs)
        expr = (body.arg(1))
        print("EXPR:: ", expr)
        return (z3.unsat, args, expr)
    else:
        return (z3.sat, None, None)

if __name__ == '__main__':
    M = TransitionSystem()
    def bad(xs):
        return [xs[0] > xs[1]]
    #fixedpoint(M, bad)

    Msc = SelfComposedTransitionSystem(M)
    def bad_sc(xs):
        return [z3.And(xs[0] == xs[2], xs[1] != xs[3])]
    # The following times out.
    #fixedpoint(Msc, bad_sc)

    relationalInduction(M, Msc, bad_sc)
