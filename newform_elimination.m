// This code follows the algorithm described in Section 5.2 of the paper.
// If the dimension of the space of newforms is > 10000 then the code is unlikely to terminate.

Cf:=function(q,e); // q a prime ideal, e a polynomial. Outputs corresponding c-value. See Remark 5.3 of the paper.
    nq:=Norm(q);
    A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
    C1:=nq * Evaluate(e,nq+1) * Evaluate(e,-nq-1) * (&*[Evaluate(e,-a) : a in A]);
    C:= AbsoluteValue(Integers() ! C1 );
    return C;
end function;

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
    print "There are", #Newind, "spaces remaining";
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
            print "All spaces eliminated after step", i;
            return Vs, Cs, Es, T;
        end if;
    end for;
    print "Spaces remaining, unable to eliminate the following primes:", Cs;
    return Vs, Cs, Es, T;
end function;


decomp_elim := function(Np,K,normbd);
    M := HilbertCuspForms(K, Np);
    NewM:=NewSubspace(M);
    decomp := NewformDecomposition(NewM);
    CNpfs:=[];
    CNpPrimes:=[];
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
        end if;
        CNpPrimes:=CNpPrimes cat CNpfPrimes;
        CNpfs:=CNpfs cat [CNpf];
    end for;
    CNpred:=SetToSequence(Set(CNpfs));
    CNpPrimes:=SetToSequence(Set(CNpPrimes));
    return CNpPrimes;
end function;


too_big_d := [39, 70, 78, 95]; // Dimensions too large for computations (some dimension > 10000)
big_d := [34, 42, 55, 66, 91];

// Note that the computations for d = 34, 42, 55, 66, 91 require a lot of memory (some dimension > 3000)
// Especially d = 55, 66 (some dimension > 7000)

for d in [d : d in [2..100] | IsSquarefree(d) and d notin (too_big_d cat big_d)] do
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
