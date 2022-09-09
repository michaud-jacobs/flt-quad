// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

////////////
// Part 1 //
////////////

// Code to calculate the possibilities for the level-lowered levels N_p

d:=95;
T<x>:=PolynomialRing(Rationals());
K<a>:=NumberField(x^2-d);   

assert IsTotallyReal(K);
ClK,mu:=ClassGroup(K);
muinv:=mu^(-1);
OK:=RingOfIntegers(K); 
Fac:=Factorisation(2*OK);
Pfacts:=[Fac[i][1] : i in [1..#Fac]]; // The set S of primes above 2.

QuoClK,nu:=quo<ClK | 2*ClK>;
elts:=[q : q in QuoClK];

H:=[1*OK];
for i in [2..#QuoClK] do 
primes := [P : P in PrimesUpTo(40,K) | IsOdd(Norm(P)) and nu(muinv(P)) eq elts[i]];
_,n:=Minimum([Norm(P) : P in primes]);
H_i:=primes[n];
H:=H cat [H_i];
end for;              // H forms a set of representatives for Cl(K)/Cl(K)^2, with #H=r.

////////////////////////////

// We now follows the strategy in [15]:  N. Freitas and S. Siksek.  Fermat’s Last Theorem over some small real quadratic fields.  Algebra & Number Theory, 9(4):875–895, 2015  to calculate a list of possible levels N_p.

// We first compute possibilities for the even part of the level.

R<y>:=PolynomialRing(K);

rams:=[Fac[i][2] : i in [1..#Fac]];  

b:=&*[(Pfacts[i])^(2*rams[i]+1) : i in [1..#Fac]];

OKb,pi:=quo<OK | b>;           

U,r:=UnitGroup(OKb);
s:=r^(-1);

Sq:={oo^2 : oo in OKb | IsUnit(oo)};
SFU,w:=quo<U |s(Sq)>;

Uni,psi:=UnitGroup(OK);

UniGens:=SetToIndexedSet(Generators(Uni));

imphi:=[pi(psi(gg)): gg in UniGens | IsUnit(pi(psi(gg)))];

Coker, v := quo<SFU | w(s(imphi))>;

reps:=[(r(  (cc @@ v   ) @@ w)) @@ pi : cc in Coker];

g:=#UniGens;
list:=[**];
for b in [0..(2^g)-1] do
l1:=Intseq(b,2);
    if g gt #l1 then 
        l2:=l1 cat ZeroSequence(Integers(),g-#l1);
    end if;
    if g eq #l1 then
       l2:=l1;
    end if;
list:=list cat [*l2*];
end for;
sfunits:=[];
for l in list do
sfunit:=&*[(psi(UniGens[i]))^(l[i]) : i in [1..#UniGens]];
sfunits:=sfunits cat [sfunit];
end for;

Lambdas:=[**];
for i in [1..#reps] do
lambi:=[sfunits[j]*reps[i] : j in [1..#sfunits]];
Lambdas:=Lambdas cat [*lambi*];
end for;

newreps:=[];
Npevens:=[];
for i in [1..#reps] do
    Npevensi:=[];
    for j in [1..#sfunits] do
        rootlam:=y^2-Lambdas[i][j];
        exps:=[];
        for k in [1..#Pfacts] do
            if IsIrreducible(rootlam) eq true then 
               L := NumberField(rootlam);
               OL:=RingOfIntegers(L);
               D:=Discriminant(OL);  
               v:=Valuation(D, Pfacts[k]);
               if v eq 0 then
                   e:=1;
               end if;
               if v gt 0 then
                   e:=2*v;
               end if;
             end if;
             if IsIrreducible(rootlam) eq false then 
                e:=1;
             end if;
             exps:=exps cat [e];
        end for;
        Npeven:=&*[Pfacts[j]^(exps[j]): j in [1..#Pfacts]];
        Npevensi:=Npevensi cat [Npeven];
     end for;
     _,pos:=Minimum([Norm(n): n in Npevensi]);
     newreps:=newreps cat [Lambdas[i][pos]];
     Npevens:=Npevens cat [Npevensi[pos]];
end for;
newrepsK:=[K ! (OK ! newreps[i]) : i in [1..#newreps]];
Vals:= [   [Valuation(Npevens[i],Pfacts[j]) : i in [1..#reps]]   : j in [1..#Pfacts]];

Npevset:=IndexedSet(Npevens); // Possibilities for the even part of N_p, when 2 is not inert in K.

if IsInert(2,OK) eq true then 
   Npevset:= Npevset join {Pfacts[1]^4};
end if;

// Combine even and odd part of N_p to give a list of possibilities for N_p.

N_ps:={};
for i in [1..#H] do
    for j in [1..#Npevset] do 
        Np:=((H[i])^2)*(Npevset[j]);
        N_ps:=N_ps join {Np};
    end for;
end for;
N_ps:=IndexedSet(N_ps);   // A list of the possible levels N_p
[Norm(P):P in N_ps];

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

/////////////
// Part 2a //
/////////////

// We now compute, as f ranges over Hilbert newforms at the different levels.
// This code computes the full newform decomposition.
// This should only be used if the maximum newform dimension is < 500 as otherwise it is unlikely to terminate.

CfsFull:=[**];
CfsRed:=[**];
CPrimes:=[**];
Decomps:=[**];
Cuspdims:=[];
Newdims:=[];
for Np in N_ps do
    M := HilbertCuspForms(K, Np);  
    NewM:=NewSubspace(M); 
    Cuspdims:=Cuspdims cat [Dimension(M)];
    Newdims:= Newdims cat [Dimension(NewM)]; 
    decomp := NewformDecomposition(NewM);
    Decomps:=Decomps cat [*decomp*]; 
    CNpfs:=[];
    CNpPrimes:=[];
    for i in [1..#decomp] do
        f:=Eigenform(decomp[i]);
        Q_f:=HeckeEigenvalueField(decomp[i]);
        OQ_f:=Integers(Q_f);
        normbd:=300;    // Increase this bound to enlarge T
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
    CfsFull:=CfsFull cat [*CNpfs*];
    CfsRed:=CfsRed cat [*CNpred*];
    CPrimes:=CPrimes cat [*CNpPrimes*];
end for;
CPrimes;   // A list of primes dividing the C_f values. If 0 appears, this corresponds to a C_f value 0.

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

/////////////
// Part 2b //
/////////////

// This code computes the newform decomposition as above, but avoids calculting Q_f and its ring of integers.
// This should only be used if the maximum newform dimension is < 800 as otherwise it is unlikely to terminate.

CfsFull:=[**];
CfsRed:=[**];
CPrimes:=[**];
Decomps:=[**];
Cuspdims:=[];
Newdims:=[];
for Np in N_ps do
    M := HilbertCuspForms(K, Np);  
    NewM:=NewSubspace(M); 
    Cuspdims:=Cuspdims cat [Dimension(M)];
    Newdims:= Newdims cat [Dimension(NewM)]; 
    decomp := NewformDecomposition(NewM);
    Decomps:=Decomps cat [*decomp*]; 
    CNpfs:=[];
    CNpPrimes:=[];
    for i in [1..#decomp] do
        f:=Eigenform(decomp[i]);
        Q_f:=HeckeEigenvalueField(decomp[i]);
        normbd:=70;    // Increase this bound to enlarge T
        T := [q : q in PrimesUpTo(normbd,K) |Valuation(Np,q) eq 0 ];
        NBqfs:={};
        for q in T do
            nq:=Norm(q);
            aqf:=HeckeEigenvalue(f,q);
            A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
            Bqf1:=nq*((nq+1)^2-aqf^2);
            Bqf2:=&*[a-aqf: a in A];
            Bqf:=(Bqf1*Bqf2);
            NBqf:= Integers() ! ( Norm(Bqf) );
            NBqfs:= NBqfs join {NBqf};
        end for;
        CNpf:=GCD(NBqfs);
        if CNpf ne 0 then
           CNpfPrimes:=PrimeFactors(CNpf);
        else CNpfPrimes:=[0];
        end if;
        CNpPrimes:=CNpPrimes cat CNpfPrimes;
        CNpfs:=CNpfs cat [CNpf];
    end for;
    CNpred:=SetToSequence(Set(CNpfs));
    CNpPrimes:=SetToSequence(Set(CNpPrimes));
    CfsFull:=CfsFull cat [*CNpfs*];
    CfsRed:=CfsRed cat [*CNpred*];
    CPrimes:=CPrimes cat [*CNpPrimes*]; CPrimes;
end for;
CPrimes;    // A list of primes dividing the C_f values. If 0 appears, this corresponds to a C_f value 0.

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

/////////////
// Part 2c //
/////////////

// This code follows the algorithm described in Section 5.2 of the paper.
// If the dimension of the space of newforms is > 10000 then the code is unlikely to terminate.

M := HilbertCuspForms(K, Np);  
NewM:=NewSubspace(M); 
normbd:=100;   // Increase this bound to enlarge T
pbd:=13;       // If all prime divisors of a c-value are <= pbd, then the subspace is eliminated.

T1 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and IsSplit(q) ];
T1 := [T1[i] : i in [1..#T1] | IsOdd(i)];
T2 := [q : q in PrimesUpTo(normbd,K) | (Valuation(Np,q) eq 0) and (IsSplit(q) eq false ) ];
T:=Sort(T1 cat T2);
#T;

Cf:=function(q,e); // q a prime ideal, e a polynomial. Outputs corresponding c-value. See Remark 5.3 of the paper.
    nq:=Norm(q); 
    A:=[a : a in [Ceiling(-2*Sqrt(nq))..Floor(2*Sqrt(nq))] | IsZero((nq+1 - a) mod 4)];
    C1:=nq * Evaluate(e,nq+1) * Evaluate(e,-nq-1) * (&*[Evaluate(e,-a) : a in A]);
    C:= AbsoluteValue(Integers() ! C1 );
    return C;
end function;

time H1:=HeckeOperator(NewM,T[1]);
M1:=Matrix(H1);
time Chpoly1:=Factorisation(CharacteristicPolynomial(H1));

Cs:=[*Cf(T[1],e[1]) : e in Chpoly1*];
Newind:=[i : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))];
Cs:=[*Cs[i] : i in Newind*];
Newind;
#Newind;
Es:=[* [Chpoly1[i][1]] : i in Newind*]; 
Vs:=[* *];
time for j in Newind do   // Start by computing the list of irreducible subspaces corresponding to the first Hecke operator
     print "Doing j = ",j; 
     V := NullSpace(Evaluate(Chpoly1[j][1],M1));
     Vs := Vs cat [* V *];
end for;

time for i in [2..#T] do     

     print "Doing i = ",i; 

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
     
     Es:=[*Es[i] : i in [1..#Es] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
     Vs:=[*Vs[i] : i in [1..#Vs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];
     Cs:=[*Cs[i] : i in [1..#Cs] | (Cs[i] eq 0) or ((Cs[i] ne 1) and (Maximum(PrimeFactors(Cs[i])) gt pbd))*];

     if #Vs eq 0 then 
        i;
        break i;
     end if;
end for;
 
// If Vs is empty then we have discarded all subspaces.
