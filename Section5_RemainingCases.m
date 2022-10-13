// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

// We carry out the computations for the image of inertia argument
// in the cases d = 34 and d = 55
// The code is very similar for each case

d := 34;
N_ps,K := Np_possibilities(d);
Np := N_ps[2]; // This is p^8, for p the prime above 2.
Vs, Cs, Es, T := eliminate_2(Np,K); // (using norm bound of 150)
assert Cs eq [* 0, 0, 753664, 753664 *];
// We want to try and eliminate the first two newforms.
// We can see the newform's eigenvalues with Es
// and the corresponding prime ideals with T
// The eigenvalues are all rational

f1 := Es[1];
e_vals_f1 := [-Evaluate(e,0) : e in f1];
// [ 0, 2, 14, 0, -2, -10, -2, 0, -10, 10, 0, 0, -6, 0, 0, 22, 0 ]
f2 := Es[2];
e_vals_f2 := [-Evaluate(e,0) : e in f2];
// [ 0, -2, 14, 0, -2, 10, 2, 0, 10, 10, 0, 0, 6, 0, 0, 22, 0 ]

// We search for elliptic curves to which these newforms corresponds
// The elliptic curve function will list isogenous curves
// and may produce many matching curves
matching_curves_f1 := [];
matching_curves_f2 := [];
Ell_curves := EllipticCurveSearch(Np,1);
for Ell in Ell_curves do
    traces := [TraceOfFrobenius(Ell,q) : q in T];
    if traces eq e_vals_f1 then
        matching_curves_f1 := matching_curves_f1 cat [Ell];
    end if;
    if traces eq e_vals_f2 then
        matching_curves_f2 := matching_curves_f2 cat [Ell];
    end if;
end for;
// We choose one matching curve for each newform
E1 := matching_curves_f1[1]; // Elliptic Curve defined by y^2 = x^3 + (10*sqrt_d - 59)*x over K
E2 := matching_curves_f2[1]; // Elliptic Curve defined by y^2 = x^3 + (-10*sqrt_d + 59)*x over K

// apriori each Ei could correspond to a newform different than fi
// however, if this were the case, there would be another newform with the same first eigenvalues
// and it therefore would have not been eliminated in the elimination step

// We check that E1 and E2 have potentially good reduction at the unique prime above 2
pp := Factorisation(Np)[1][1];
j1 := jInvariant(E1);
j2 := jInvariant(E2);
assert Valuation(j1,pp) ge 0;
assert Valuation(j2,pp) ge 0;

/////////////////////////////////////////////////
/////////////////////////////////////////////////

// We repeat the above calculations for d = 55

d := 55;
N_ps,K := Np_possibilities(d);
Np := N_ps[3]; // This is p^8, for p the prime above 2.
Vs, Cs, Es, T := eliminate_2(Np,K); // (using norm bound of 150)
assert Cs eq [* 0, 0, 184 *];
f1 := Es[1];
e_vals_f1 := [-Evaluate(e,0) : e in f1];
// [ 0, 2, -14, 0, 6, -2, 0, 0, 0, 0, 6, 0, 10, 0, 0, 0 ]
f2 := Es[2];
e_vals_f2 := [-Evaluate(e,0) : e in f2];
// [ 0, 2, -14, 0, -6, 2, 0, 0, 0, 0, -6, 0, 10, 0, 0, 0 ]

matching_curves_f1 := [];
matching_curves_f2 := [];
Ell_curves := EllipticCurveSearch(Np,1);
for Ell in Ell_curves do
    traces := [TraceOfFrobenius(Ell,q) : q in T];
    if traces eq e_vals_f1 then
        matching_curves_f1 := matching_curves_f1 cat [Ell];
    end if;
    if traces eq e_vals_f2 then
        matching_curves_f2 := matching_curves_f2 cat [Ell];
    end if;
end for;

E1 := matching_curves_f1[1]; // Elliptic Curve defined by y^2 = x^3 + (2136*sqrt_d + 15841)*x over K
E2 := matching_curves_f2[1]; // Elliptic Curve defined by y^2 = x^3 + x over K

pp := Factorisation(Np)[1][1];
j1 := jInvariant(E1);
j2 := jInvariant(E2);
assert Valuation(j1,pp) ge 0;
assert Valuation(j2,pp) ge 0;













// This code carries out the computations of Lemma 5.5 in the paper.

for d in [57,89] do
U<x>:=PolynomialRing(Rationals());
K<a>:=NumberField(x^2-d);
OK:=Integers(K);

PP:=PrimesInInterval(17,10^6);  // Primes to test
ns:=[];    // For each prime we aim to find a value of n that works.
time for p in PP do;
    nsp:=[];
    for n in [1..p-3] do
        if  ((n mod 4) eq 2) and (IsPrime(n*p+1)) and  (IsSplit(n*p+1,OK)) then
            q:=n*p+1;
            S<z>:=PolynomialRing(GF(q));
            if Resultant(z^n-1,   (z+1)^n-1) ne 0 then
               nsp:= nsp cat [n];
            break n;
            end if;
        end if;
    end for;
    ns:=ns cat [nsp];
end for;

#[i : i in [1..#ns] |#ns[i] eq 0];
badp:=[PP[i] : i in [1..#ns] |#ns[i] eq 0];  // A list of primes for which we cannot obtain such an n.
badp;
end for;


// In these cases we work directly with the Hilbert newforms with c-values 0 and try and find a suitable n for each prime p.

Gns:=[];  // ns that work for the bad primes.
for p in badp do
    p;
    // We can alter the range of n here
    qs:=[ n*p+1: n in [1..200] | (IsPrime(n*p+1)) and (IsSplit(n*p+1,OK)) and( (Integers()!(Resultant(x^n-1,(x+1)^n-1)) mod (n*p+1)) ne 0)];
    q:=qs[1]; // a choice of prime q. Usually the first prime works.
    n:=(q-1)/p;
    Gns:=Gns cat [n];
    qq:=Factorisation(q*OK)[1][1];
    h1:=Integers() ! (HeckeEigenvalue(f1,qq)) mod p;
    assert h1 ne 2;     // If this holds, then n works
end for;

// We list below the bad primes for each value d considered and values of n that work to eliminate them.

// d = 17:       31, 43, 53, 61, 67, 137, 157, 167
// n:            46, 40, 74, 16, 70, 8,   76,  128

// d = 33:       19, 23, 29, 31, 37, 67, 73, 139, 379
// n:            40, 20, 8,  46, 4,  28, 4,  4,   52

// d = 41:       17, 19, 23, 31, 37, 47, 59, 61, 83, 97, 137, 283, 523
// n:            26, 22, 20, 46, 40, 20, 20, 76, 32, 4,  8,   40,  16

// d = 57:       17, 19, 23, 31, 37, 41, 61, 67, 71, 101, 199, 257, 283
// n:            98  NA, 26, 46, 40, 68, 16, 4,  8,  56,  4,   176, 172   (no value of n found for p = 19)

// d = 89:       17, 19, 29, 37, 41,  127, 137, 139, 157, 163, 193, 227
// n:            26, 40, 8,  40, 56*, 4,   20,  52,  28,  64,  52,  176
