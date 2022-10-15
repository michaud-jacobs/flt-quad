// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is in the newform_elimination_output.txt file

// This code attemptes to eliminate all newforms at all possible levels
// There are two functions for this, hecke_elim and decomp_elim

// hecke_elim works directly with Hecke operators to compute partial newform fundamental
// as the levels get larger (say > 200) it is much faster
// as the levels get even larger (say >1000), it is the only option.

// decomp_elim computes the full newform decompositions
// it should only be used on spaces of smaller dimensions
// it has a greater chance of eliminating primes than hecke_elim

// the functions in this file rely on the Np_possibilities functions in the levels.m file

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// auxiliary function to compute c-values
// q a prime ideal, e a polynomial. Outputs corresponding c-value. See Remark 5.3 of the paper.

Cf:=function(q,e);
    nq:=Norm(q);
    A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
    C1:=nq * Evaluate(e,nq+1) * Evaluate(e,-nq-1) * (&*[Evaluate(e,-a) : a in A]);
    C:= AbsoluteValue(Integers() ! C1 );
    return C;
end function;

// hecke_elim works directly with Hecke operators to try and eliminate newforms
// Input: Level Np and quadratic field K
// Output:
// Vs: subspaces of the space of newforms that were not eliminated0
// Cs: corresponding c-values of these subspaces
// Es: corresponding characteristic polynomials of these subspaces
// T: list of primes used

hecke_elim := function(Np,K);
    M := HilbertCuspForms(K, Np);
    NewM:=NewSubspace(M);
    normbd:=150;   // Increase this bound to enlarge T
    pbd:=13;       // If all prime divisors of a c-value are <= pbd, then the subspace is eliminated.

    T1 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and IsSplit(q) ];
    T1 := [T1[i] : i in [1..#T1] | IsOdd(i)];
    T2 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and (IsSplit(q) eq false ) ];
    T:=Sort(T1 cat T2);
    print "Using", #T, "primes";
    print "Computing first Hecke operator";
    H1:=HeckeOperator(NewM,T[1]);
    M1:=Matrix(H1);
    print "Factorising its characteristic polynomial";
    Chpoly1:=Factorisation(CharacteristicPolynomial(H1));

    Cs:=[*Cf(T[1],e[1]) : e in Chpoly1*];
    Newind:=[i : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))];
    Cs:=[*Cs[i] : i in Newind*];
    Es:=[* [Chpoly1[i][1]] : i in Newind*];
    Vs:=[* *];
    print "Computing first Hecke decomposition";
    for j in Newind do   // Start by computing the list of irreducible subspaces corresponding to the first Hecke operator
        V := NullSpace(Evaluate(Chpoly1[j][1],M1));
        Vs := Vs cat [* V *];
    end for;
    print "Computing further Hecke decompositions";
    for i in [2..#T] do
        H:=HeckeOperator(NewM,T[i]);
        M:=Matrix(H);
        NVs:=[* *];
        NCs:=[* *];
        NEs:=[* *];
        for j in [1..#Vs] do
            B:=Basis(Vs[j]);
            Coords:=[Coordinates(Vs[j],H(B[k])) : k in [1..#B]   ];
            NM:=Matrix(Coords);
            Chpoly:=Factorisation(CharacteristicPolynomial(NM));
            NVsj:=[* *];
            NCsj:=[* *];
            NEsj:=[* *];
            for e in Chpoly do
                basns:= Basis(  NullSpace( Evaluate(e[1],NM) )  );
                subsp:= sub< Vs[j] | [ &+[basns[l][k]*B[k] : k in [1..#B] ]  :  l in [1..#basns] ]>;
                NVsj:=NVsj cat [* subsp *];
                NC:= GCD(  Cs[j],Cf(T[i],e[1])   ); // gcd of previous norm and new norm
                NCsj:=NCsj cat [* NC *];
                Ne:=Es[j] cat [e[1]];
                NEsj:=NEsj cat [* Ne *];
            end for;
            NVs:=NVs cat NVsj;
            NCs:=NCs cat NCsj;
            NEs:=NEs cat NEsj;
        end for;
        Vs:=NVs;
        Cs:=NCs;
        Es:=NEs;
        // We now eliminate subspaces
        Vs:=[*Vs[i] : i in [1..#Vs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        Es:=[*Es[i] : i in [1..#Es] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        Cs:=[*Cs[i] : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
        if #Vs eq 0 then
            print "All spaces eliminated";
            return Vs, Cs, Es, T;
        end if;
    end for;
    print "Spaces remaining, unable to eliminate the following primes:", Cs;
    return Vs, Cs, Es, T;
end function;

// decomp_elim computes the full newform decomposition to try and eliminate newforms
// Input: Level Np, quadratic field K, normbd to control how many primes to use
// Output:
// CNpprimes: primes that were not eliminated,
//            a zero means no primes were eliminated for the corresponding form
// bad_f: a list of newforms with c_value = 0
// T: list of primes used

decomp_elim := function(Np,K,normbd);
    M := HilbertCuspForms(K, Np);
    NewM:=NewSubspace(M);
    decomp := NewformDecomposition(NewM);
    CNpfs:=[];
    CNpPrimes:=[];
    bad_f := [* *];
    for i in [1..#decomp] do
        f:=Eigenform(decomp[i]);
        Q_f:=HeckeEigenvalueField(decomp[i]);
        OQ_f:=Integers(Q_f);
        T := [q : q in PrimesUpTo(normbd,K) |Valuation(Np,q) eq 0 ];
        Bqfs:={};
        for q in T do
            nq:=Norm(q);
            aqf:=HeckeEigenvalue(f,q);
            A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
            Bqf1:=nq*((nq+1)^2-aqf^2);
            Bqf2:=&*[a-aqf: a in A];
            Bqf:=(Bqf1*Bqf2)*OQ_f;
            Bqfs:=Bqfs join {Bqf};
        end for;
        Bf:=&+Bqfs;
        if Bf ne 0*OQ_f then
           CNpf:=Norm(Bf);
           CNpfPrimes:=PrimeFactors(CNpf);
        else CNpf:=0;
             CNpfPrimes:=[0];
             bad_f := bad_f cat [* f *];
        end if;
        CNpPrimes:=CNpPrimes cat CNpfPrimes;
        CNpfs:=CNpfs cat [CNpf];
    end for;
    CNpred:=SetToSequence(Set(CNpfs));
    CNpPrimes:=SetToSequence(Set(CNpPrimes));
    return CNpPrimes, bad_f, T;
end function;


too_big_d := [39, 70, 78, 95]; // Dimensions too large for computations (some dimension > 10000)

// Note that the computations for d = 34, 42, 55, 66, 91 require a lot of memory (some dimension > 3000)
// Especially d = 55, 66 (some dimension > 7000)

// We now eliminate newforms
// We start by only using hecke_elim

// We include data for 1 < d < 25 to compare with Freitas and Siksek's paper
// The output is available in the newform_elimination_output.txt file


for d in [d : d in [2..100] | IsSquarefree(d) and d notin (too_big_d)] do
    print "Considering d = ", d;
    N_ps, K := Np_possibilities(d);
    for Np in N_ps do
        print "Considering level Np with factorisation:", Factorisation(Np);
        elim := hecke_elim(Np,K);
        print "+++++++++++++++++++++++++++++++++++++++++++++++++";
    end for;
    print "====================================================================";
    print "====================================================================";
    print "====================================================================";
end for;

// We now use decomp_elim to eliminate the following triples (d,p,Np):
// (d,p,Np) = (67,19,N_ps[2]) and (d,p) = (55,17,N_ps[4])
// We note we could also eliminate these two pairs (d,p)
// using the methods of Section 6, as they are d-regular.

d := 67;
N_ps, K := Np_possibilities(d);
Np := N_ps[2];
bad_primes := decomp_elim(Np,K,100); // [ 2, 3, 5, 7, 11 ]
assert 19 notin bad_primes;

d := 55;
N_ps, K := Np_possibilities(d);
Np := N_ps[4];
bad_primes := decomp_elim(Np,K,100); // [ 2, 3 ]
assert 17 notin bad_primes;
