// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is in the irreducibility_output.txt file
// Some output is included within this file

// This code carries out many of the irreducibility checks of Section 3 of the paper
// The code carries out the following checks:

// Computation of ray class group exponents
//

// the functions in this file rely on the Np_possibilities functions in the levels.m file

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function computes the possible ray class group exponents

ray_class_group_exponents := function(d);
    N_ps, K := Np_possibilities(d);
    Nthetas:={@ @};   // First obtain the list of possibilities for N_theta
    for Np in N_ps do
        NpFac:=Factorisation(Np);
        Npfactors:=[NpFac[i][1] : i in [1..#NpFac]];
        Npadd:=[P : P in Npfactors | IsEven(Valuation(Np,P))];
        if #Npadd ne 0 then
            Ntheta:=&*[P^(Integers() ! (Valuation(Np,P)/2)):P in Npadd];
            Nthetas:=Nthetas join {@ Ntheta @};
        end if;
    end for;

    RayCGs:={@ @};  // Then obtain a list of possible ray class groups.
    if #Nthetas ne 0 then
        for N in Nthetas do
            NthetaFac:=Factorisation(N);
            Nthetafactors:=[NthetaFac[i][1] : i in [1..#NthetaFac]];
            modu:=(&+[(Valuation(N,P))*Place(P) : P in Nthetafactors])+(&+(RealPlaces(K)));
            RayCG:=RayClassGroup(modu);
            RayCGs:=RayCGs join {@ RayCG @};
        end for;
    end if;
    if #Nthetas eq 0 then
        modu:=&+(RealPlaces(K));
        RayCG:=RayClassGroup(modu);
        RayCGs:=RayCGs join {@ RayCG @};
    end if;
    exponents := {Exponent(rcg) : rcg in RayCGs};
    return exponents;
end function;

// We compute the possible ray class group exponents for each d
// We include 1 < d < 25 to compare with Freitas and Siksek's paper

// See irreducibility_output.txt for the output of this loop

big_rcgs := []; // Form list of ds with a ray class group having exponent 8.
for d in [d : d in [2..100] | IsSquarefree(d)] do
    rcg_exps := ray_class_group_exponents(d);
    if 8 in rcg_exps then
        big_rcgs := big_rcgs cat [d];
    end if;
    print "RCG exponents for d =",d, "are", rcg_exps;
end for;

// These are the ds with a ray class group having exponent 8.
big_rcgs := [ 26, 34, 35, 39, 55, 82, 91, 95 ];

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function implements the computation described in Lemma 3.8
// Input: squarefree d > 0
// Output: list of bad primes > 20 in the non-coprime split case

bad_p_split := function(d);
    K := QuadraticField(d);
    OK := Integers(K);
    Uni,psi:=UnitGroup(OK);
    if IsInert(2,OK) then
        n:=6;
    else n:=2;
    end if;

    v:=psi(Uni.2);

    if IsTotallyPositive(v) or IsTotallyPositive(-v) then
        u:=v;
    else u:=v^2;
    end if;
    FactNorm:=PrimeFactors(Norm(u^n-1));
    Spl:=[p : p in FactNorm | IsSplit(p,OK) and p gt 20];
    return Spl;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function implements the computation described in Proposition 3.6
// It is only necessary to run this code for d with a ray class group exponent 8
// Input: squarefree d > 0
// Output: list of bad primes > 20 in the coprime case

bad_p_for_big_rcgs:= function(d);
    T<x>:=PolynomialRing(Rationals());
    K<a>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    Uni,psi:=UnitGroup(OK);
    v:=psi(Uni.2);  // v = epsilon, the fundamental unit of K
    B:=PrimeFactors(Integers() ! (Norm(v^12-1))); // The prime factors of the quantity B = Norm(epsilon^12-1)

    // We now choose the set T.
    // We must exclude q divides m here if m is a prime of char > 5).
    N_ps,_,_,H := Np_possibilities(d);
    if #H eq 2 then
        m := H[2];
        char_m := PrimeFactors(Integers()! Norm(m))[1];
    end if;
    // Increasing normbd1 enlarges the set T.
    normbd1:=10000;
    T:=[q : q in PrimesUpTo(normbd1,K) |  IsSplit(q) eq false and PrimeFactors(Integers() ! (Norm(q)))[1] gt 5 and PrimeFactors(Integers() ! (Norm(q)))[1] ne char_m];

    // we compute the values R_q for q in T
    Resus:=[];
    for q in T do
        if IsPrincipal(OK !! q) then
            r:=1;
        else r:=2;
        end if;

        nq:=Norm(q);
        A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
        Ressq:=[];
        for i in [1..#A] do
            a:=A[i];
            Res:= Resultant(x^2-a*x+nq,x^(12*r)-1);
            Ressq:=Ressq cat [Res];
            if i eq #A then
                Ressq:=Ressq cat PrimeFactors(nq); // we also include the rational prime below q here;
            end if;
        end for;
        Resus:=Resus cat [Integers() ! (&*Ressq)];
    end for;
    R:=[p : p in PrimeFactors(GCD(Resus))];

    badp:= Set(B cat R cat PrimeFactors(Discriminant(OK)));
    vbadp:={ p : p in badp | p gt 19 and p lt 6724} join {37}; // Can apply Oesterle's bound here.
    return vbadp;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// We combine the functions above to compute an initial list of bad primes for each d
// Input: squarefree d > 0
// Output: Initial list of bad primes > 20

all_bad_primes_1 := function(d);
    bad_split := Set(bad_p_split(d));
    K := QuadraticField(d);
    OK := Integers(K);
    if IsInert(2,OK) then // Must also consider the ramified primes
        ram_p := {p : p in PrimeFactors(Discriminant(Integers(K))) | p gt 20};
    else ram_p := {};
    end if;
    if d in big_rcgs then
        rcg_bad_p := bad_p_for_big_rcgs(d);
    else rcg_bad_p := {};
    end if;
    all_bad_p := bad_split join ram_p join rcg_bad_p;
    return all_bad_p, bad_split, ram_p, rcg_bad_p;
end function;

// We compute an initial list of bad primes for each d
// See the file irreducbility_output.txt for the output of this loop

for d in [d : d in [2..100] | IsSquarefree(d)] do
    print "Considering d =", d;
    all_bad_p, bad_split, ram_p, rcg_bad_p := all_bad_primes_1(d);
    print "The bad split primes in not coprime case are:", bad_split;
    print "The bad ramified primes are:", ram_p;
    print "The big RCG bad primes are:", rcg_bad_p;
    print "All bad primes > 19 (part 1) are:", all_bad_p;
    print "++++++++++++++++++++++++++++++";
end for;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function implements the computation described in Lemma 2.3

// Input: d, p, bd (a search bound)
// Output: A list of primes
// Each prime splits in K = Q(sqrt_d) and the two primes of K above it are of multiplicative reduction for E_{a,b,c,p}

mult_primes_q := function(d,p,bd);
    U<x>:=PolynomialRing(Rationals());
    K := QuadraticField(d);
    OK:=Integers(K);
    qs:= [ n*p+1: n in [1..bd] | (IsPrime(n*p+1)) and (IsSplit(n*p+1,OK)) and  ( (Integers() ! (Resultant(x^n-1,(x+1)^n-1)) mod (n*p+1)) ne 0  ) ];
    return qs;
end function;

// We try and find for each pair (d,p) with p a bad prime a prime of multipliactive reduction
// Output included below the loop and in the irreducibility_output.txt file

for d in [d : d in [2..100] | IsSquarefree(d)] do
    all_bad_p := all_bad_primes_1(d);
    for p in all_bad_p do
        mult := mult_primes_q(d,p,100);
        if mult eq [] then
            print "No prime found when d =",d, "and p=",p;
        end if;
    end for;
end for;

/* Output:

No prime found when d = 69 and p= 23
No prime found when d = 93 and p= 31

*/

// Although we found nothing in the cases (d,p) = (69,23) and (93,31)
// The curves X_0(23) and X_0(31) have no non-exceptional points over the corresponding quadratic fields
// So the conclusion is the same as when we can find primes of multiplicative reduction

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function implements the computation described in Theorem 4.3

// Input: d, p
// Output: 0 or 1
// If 0, the test failed and X_0(p)^d(Q) may have a rational point
// If 0, the test failed and X_0(p)^d(Q) has no rational points

twist_check := function(d,p);
    pass := 0;
    K := QuadraticField(d);
    OK := Integers(K);
    M := QuadraticField(-p);
    OM := Integers(M);
    ls := [l : l in PrimeFactors(Discriminant(OK)) | IsZero(p mod l) eq false];
    for l in ls do
        ll := Factorisation(l*OM)[1][1];
        if IsPrincipal(ll) eq false then
            pass := 1;
            break;
        end if;
    end for;
    return pass;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This function uses the twist_check function to output a list of bad primes

all_bad_primes_2 := function(d);
    all_bad_1 := all_bad_primes_1(d);
    all_bad_2 := {};
    for p in all_bad_1 do
        if twist_check(d,p) eq 0 and p ne 37 then
            all_bad_2 := all_bad_2 join {p};
        end if;
    end for;
    return all_bad_2;
end function;

// See the file irreducibility_output.txt for the output of this loop

for d in [d : d in [2..100] | IsSquarefree(d)] do
    all_bad_2 := all_bad_primes_2(d);
    if all_bad_2 ne {} then
        print "For d =",d,"all bad primes > 19 (part 2) are:", all_bad_2;
    end if;
end for;

// We are left with the following pairs (d,p) to Considering

// (d,p) = (29,29), (34,59), (53,53), (61,61), (71,59), (74,43), (89,53), (91,67), (93,31)

// We consider (d,p) = (29,29), (34,59), (53,53), (89,53) in the modular_parametrisation file
// We consider (d,p) = (61,61) and (74,43) in the sieve file

// It remains to consider (d,p) = (71,59), (91,67), (93,31)

// The classification of all quadratic points on X_0(67) rules out (d,p) = (91,67):
// J. Box. Quadratic points on modular curves with infinite Mordell–Weil group. Mathematics of Computation, 90(327):321–343, 2020.

// The classification of all quadratic points on X_0(62) rules out (d,p) = (93,31):
// F. Najman and B. Vukorepa. Quadratic points on bielliptic modular curves. https://arxiv.org/abs/2112.03226

// Finally, for (d,p) = (34,59) and (71,59), we prove that the hyperelliptic curve X_0(59) twisted by d has no rational points

for d in [34,71] do:
    X := SimplifiedModel(SmallModularCurve(59));
    Xd := QuadraticTwist(X,d);
    s := TwoCoverDescent(Xd); // Computes the fake 2-Selmer set, about 30 mins.
    assert s eq {}; // So no rational points
end for;
