# Sage code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

# This code carries out the eta product method described in Section 4.2 of the paper

E = EllipticCurve('116b1') 
assert E.rank() == 0
Tors = E.torsion_subgroup()
Pts = [E(t) for t in Tors]
NPts = len(Pts) # size of the torsion subgroup.
d = 29
Ed = E.quadratic_twist(d)
assert Ed.rank() == 0
K.<z> = NumberField(x^2-d) 
EK = E.change_ring(K)
TorsK = EK.torsion_subgroup()
PtsK = [EK(t) for t in Tors]
NPtsK = len(PtsK)
assert NPts == NPtsK # torsion subgroup over K is same as over Q.
#
precbd = 3000 # precision to be used.
N = E.conductor()
m = E.modular_degree()
phi = E.modular_parametrization() 
xq = (phi.power_series(prec = precbd))[0] # q expansion of pullback of x-coordinate up to wanted precision.
Etas = EtaGroup(N).basis() # Basis for the eta products at level N.
s = Etas[1]  #  A choice of eta product.
I = s.degree() #  degree as a rational function on X_0(N).
sq =  s.qexp(precbd) #  q-expansion up to desired precision.
#
L.<q> = LaurentSeriesRing(QQ, default_prec = precbd) 
xq = L.coerce(xq)
sq = L.coerce(sq)
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
#
F = gcd(eqns) 
F = F * (1 / (F.coefficients()[0])) 
F.degree(X) - I   
F.degree(S) - 2*m  # both quantities will be 0 if planar model.
assert len(F.factor())==1 # F is irreducible
G = F(1/X,S).numerator()  # To work with poles.
F2 = F(X,1/S).numerator()
G2 = G(X,1/S).numerator()
#
Fs = F(0,S).factor(); Fs # Substitute in x-coordinate
Gs = G(0,S).factor(); Gs # Substitute in 1/(x-coordinate)
F2s = F2(0,S).factor(); F2s # Missing poles
G2s = G2(0,S).factor(); G2s
#
M.<y> = NumberField(x^2-2) 
M.discriminant()
M.optimized_representation() # obtain nice representation of field of definition of s-value
