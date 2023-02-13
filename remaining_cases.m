// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is in the remaining_cases_output.txt file
// Some output is included within this file

// This code carries out the remaining elimination steps in Section 5 of the paper
// The code carries out the following checks:

// Image of inertia argument for d = 34 and d = 55
// Symplectic argument for d = 89
// Sieving steps for eliminating individual primes p

// the functions in this file rely on the Np_possibilities functions in the levels.m file
// and all functions in the newform_elimination.m file.

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// We carry out the computations for the image of inertia argument
// in the cases d = 34 and d = 55
// The code is very similar for each case

d := 34;
N_ps,K := Np_possibilities(d);
Np := N_ps[2]; // This is p^8, for p the prime above 2.
Vs, Cs, Es, T := hecke_elim(Np,K); // (using norm bound of 150)
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
// The elliptic curve function may list isogenous curves
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
Vs, Cs, Es, T := hecke_elim(Np,K); // (using norm bound of 150)
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


///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// We verify the mod 5 case when d = 89, this is the symplectic argument

d := 89;
N_ps, K := Np_possibilities(d);
assert #N_ps eq 1;
Np := N_ps[1];
normbd := 100;
_, bad_f, T := decomp_elim(Np,K,normbd);
assert #bad_f eq 1;
f := bad_f[1];
traces_f := [HeckeEigenvalue(f,q) : q in T];
// [ -2, -2, 6, 0, 0, 2, 2, 8, 8, -6, -6, -6, 8, 8, -8, -8, 14, 14, 16, 16, -6, -2, -2 ]
Ell_curves := EllipticCurveSearch(Np,400: Primes := T, Traces := traces_f); // 30 seconds
E := Ell_curves[1];
// Elliptic Curve defined by y^2 + x*y = x^3 - x^2 + 1/2*(72875*sqrt_d - 687501)*x + 1/2*(-20764677*sqrt_d + 195893571) over K
assert E eq MinimalModel(E);
assert [TraceOfFrobenius(E,q) : q in T] eq traces_f;
p1 := Factorisation(Np)[1][1];
p2 := Factorisation(Np)[2][1];
Valuation(Discriminant(E),p1)*Valuation(Discriminant(E),p2) eq 20;

// We then consider when the quantity ((-8+2pt1)*(-8+2pt2) / 20) mod p is a square (for p >5)
// This is a square if and only if 5 is a square mod p
// This occurs if and only if p = +1 or -1 mod p
// So there are no solutions if p = +2 or -2 mod p

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// This code carries out the computations of Lemma 5.5 in the paper.

// Input: d
// Output: primes in the range 17 to 10^7 that cannot be eliminated
// when the Frey curve corresponds to a newform with rational eigenvalues

initial_bad_p := function(d);
    U<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    OK:=Integers(K);
    PP:=PrimesInInterval(17,10^7);  // Primes to test
    ns:=[];    // For each prime we aim to find a value of n that works.
    for p in PP do;
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
    badp:=[PP[i] : i in [1..#ns] |#ns[i] eq 0];  // A list of primes for which we cannot obtain such an n.
    return badp;
end function;

// A second function to try and eliminate any primes that initial_bad_p did not eliminated

// Input: p, rational newform f, field K = Q(sqrt_d)
// Output: integer n used to eliminate p if found, 0 otherwise

elim_p := function(p,f,K);
    U<x>:=PolynomialRing(Rationals());
    OK := Integers(K);
    qs:=[ n*p+1: n in [1..200] | (IsPrime(n*p+1)) and (IsSplit(n*p+1,OK)) and( (Integers()!(Resultant(x^n-1,(x+1)^n-1)) mod (n*p+1)) ne 0)];
    for q in qs do
        n:=(q-1)/p;
        qq:=Factorisation(q*OK)[1][1];
        h1:=Integers() ! (HeckeEigenvalue(f,qq));
        if h1 ne 2 and h1 ne -2 then
            print "Eliminated",p, "using n = ", n;
            return n;
        end if;
    end for;
    print "Unable to eliminate",p;
    return 0;
end function;

// We run these elimination steps for those d appearing in Theorem 3
// The output is in the remaining_cases_output.txt file

for d in [17,33,41,57,89] do
    print "Considering d = ",d;
    init_bad_p := initial_bad_p(d);
    "Initial bad primes are:", init_bad_p;
    N_ps, K := Np_possibilities(d);
    for Np in N_ps do
        C_primes, bad_f := decomp_elim(Np,K,100);
        i := 1;
        for f in bad_f do
            print "Considering newform", i;
            i := i+1;
            for p in init_bad_p do
                n := elim_p(p,f,K);
            end for;
        end for;
    end for;
    print "+++++++++++++++++++++++++++++++";
end for;
