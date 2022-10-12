# Sage code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

# This code carries out the eta product method described in Section 4.2 of the paper

# Checks if elliptic curve satisfies E(K) = E(Q)_tors

def check_ell_curve(d,E):
    rank_Q = E.rank()
    if rank_Q > 0:
        return False
    Ed = E.quadratic_twist(d)
    rank_d = Ed.rank()
    if rank_d >0:
        return False
    Q_pts = [E(t) for t in E.torsion_subgroup()]
    K.<z> = NumberField(x^2-d)
    EK = E.change_ring(K)
    K_pts = [EK(t) for t in EK.torsion_subgroup()]
    if len(Q_pts) != len(K_pts):
        return False
    return True



def F_polys(E,break_op):
    F_polys = []
    N = E.conductor()
    m = E.modular_degree()
    phi = E.modular_parametrization()
    Etas = EtaGroup(N).basis() # Basis for the eta products at level N.
    for s in Etas:
        I = s.degree() # degree as a rational function on X_0(N).
        precbd = 2*(2*m)*I + 20 # precision to be used.
        xq = (phi.power_series(prec = precbd))[0] # q expansion of pullback of x-coordinate up to wanted precision.
        sq =  s.qexp(precbd) #  q-expansion up to desired precision.
        L.<q> = LaurentSeriesRing(QQ, default_prec = precbd)
        xq = L.coerce(xq)
        sq = L.coerce(sq)
        assert 20 > sq.valuation()
        B =[xq,sq]
        R.<X,S> = QQ[]
        #
        nmons = monomials([X,S], [I+1,2*m+1])
        monsq = [L.coerce(f(xq,sq)) for f in nmons]
        #
        V = VectorSpace(QQ, len(monsq))
        W = VectorSpace(QQ,201 + len(monsq))
        h = linear_transformation(V,W,[ W ([ monsq[i][j] for j in [-200..len(monsq)]]) for i in [0..len(monsq)-1]])
        K = h.kernel()
        eqns = [ sum([k[j]*nmons[j] for j in [0..len(monsq)-1]]) for k in K.basis() ] # usually only one equation
        F = gcd(eqns)
        F = F*(1/(F.coefficients()[0]))
        # Check degrees and irreducibility
        if F.degree(X) - I == 0 and F.degree(S) - 2*m == 0 and len(F.factor())==1:
            F_polys.append(F)
            if break_op == True:
                return F_polys
    return F_polys



def fields(F, x_coord):
    R.<X,S> = QQ[]
    if x_coord == 'inf':
        G = F(1/X,S).numerator()
        G2 = G(X,1/S).numerator()
        Gs = G(0,S).factor()
        G2s = G2(0,S).factor()
        return Gs, G2s
    else:
        F2 = F(X,1/S).numerator()
        Fs = F(x_coord,S).factor()
        F2s = F2(x_coord,S).factor()
        return Fs, F2s

# We use this method for the following pairs (d,p):
# (29,29), (34,59), (53,53), (71,59), (89,53), (93,31)

################################################

# (d,p) = (29,29)
# This is the example provided in the paper
# It is the most complicated example
# We simply recreate the computations here
# and refer to the paper for the argument

d = 29
E = EllipticCurve('116b1')
assert check_ell_curve(d,E) == True
pts = [E(t) for t in E.torsion_subgroup()]
# [(0 : 1 : 0), (0 : 2 : 1), (0 : -2 : 1)]

Fs = F_polys(E, False)

F2 = Fs[0]
F5 = Fs[3]

fields2a = fields(F2,0)
# ((-4096) * (S - 2)^2 * S^3 * (S^2 + 2*S + 2) * (S^2 - 8*S + 8)^2 * (S^4 - 4*S^3 + 6*S^2 - 4*S + 2),
# (-4096) * S * (2*S - 1)^2 * (2*S^2 + 2*S + 1) * (8*S^2 - 8*S + 1)^2 * (2*S^4 - 4*S^3 + 6*S^2 - 4*S + 1))
fields2b = fields(F2,'inf')
# (S^2 * (S^2 + 2*S + 2)^2 * (S^4 - 4*S^3 + 6*S^2 - 4*S + 2)^2,
# S^2 * (2*S^2 + 2*S + 1)^2 * (2*S^4 - 4*S^3 + 6*S^2 - 4*S + 1)^2)
fields5a = fields(F5,0)
# ((16384) * S * (S + 1) * (S + 29) * (S^2 + 4*S + 29) * (S^2 + 10*S + 29) * (S^2 - 10*S + 29)^2 * (S^4 - 28*S^3 + 272*S^2 - 812*S + 841),
# (16384) * S * (S + 1) * (29*S + 1) * (29*S^2 + 4*S + 1) * (29*S^2 + 10*S + 1) * (29*S^2 - 10*S + 1)^2 * (841*S^4 - 812*S^3 + 272*S^2 - 28*S + 1))

################################################

# (d,p) = (34,59)

d = 34
E = EllipticCurve('118c1')
assert check_ell_curve(d,E) == True
pts = [E(t) for t in E.torsion_subgroup()]
# [(0 : 1 : 0)]
Fs = F_polys(E, True)
fields(Fs[0],'inf')
# ((1/48469444) * S^4 * (6962*S^2 - 120*S + 1)^2,
# (1/48469444) * S^4 * (S^2 - 120*S + 6962)^2)

# It suffices to check that the pair of quadratic points is not defined over Q(sqrt(d))
M.<y> = NumberField(x^2-120*x+6962)
M.discriminant() # -8, so not Q(sqrt(d))

################################################

# (d,p) = (53,53) AND (89,53)

E = EllipticCurve('106d1')
for d in [53,89]:
    assert check_ell_curve(d,E) == True

pts = [E(t) for t in E.torsion_subgroup()]
# [(0 : 1 : 0)]
Fs = F_polys(E, True)
fields(Fs[0],'inf')
# (S^4 * (S^6 - 46*S^5 + 48*S^4 - 600*S^3 - 192*S^2 - 736*S - 64)^2,
#  S^4 * (64*S^6 + 736*S^5 + 192*S^4 + 600*S^3 - 48*S^2 + 46*S - 1)^2)

# No quadratic points.

################################################

# (d,p) = (71,59)

d = 71
E = EllipticCurve('118d1')
assert check_ell_curve(d,E) == True # This is quite slow with Sage, it is much faster to check the rank of the twist with Magma
pts = [E(t) for t in E.torsion_subgroup()]
# [(0 : 1 : 0)]
Fs = F_polys(E, True)
fields(Fs[0],'inf')

# It suffices to check that the pair of quadratic points is not defined over Q(sqrt(d))
M.<y> = NumberField(x^2-2*x+4)
M.discriminant() # -3, so not Q(sqrt(d))

################################################
