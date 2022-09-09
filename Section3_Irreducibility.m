// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

// This code carries out the irreducibility checks in Section 3 of the paper.


////////////
// Part 1 //
////////////

// Start with a list of possible levels Np, as obtained using the code in the file Np_and_newforms.m
// This Lemma calculates the possible ray class groups (see Lemma 3.2 of the paper)

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

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

////////////
// Part 2 //
////////////

// This code implements the computation described in Lemma 3.8

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


/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

////////////
// Part 3 //
////////////

// This code implements the computations of Proposition 3.6

d:=95;
T<x>:=PolynomialRing(Rationals());
K<a>:=NumberField(x^2-d);
OK:=RingOfIntegers(K); 
Uni,psi:=UnitGroup(OK);
v:=psi(Uni.2);  // v = epsilon, the fundamental unit of K
B:=PrimeFactors(Integers() ! (Norm(v^12-1))); // The prime factors of the quantity B = Norm(epsilon^12-1)

// We now choose the set T. Increasing normbd1 enlarges the set T. 

normbd1:=10000;  
T:=[q : q in PrimesUpTo(normbd1,K) |  IsSplit(q) eq false and PrimeFactors(Integers() ! (Norm(q)))[1] gt 5 ]; // Also exclude q = m here if necessary (if m is a prime of char > 5).

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
vbadp:={ p : p in badp | p gt 19 };
vbadp;

/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

////////////
// Part 4 //
////////////

// This code implements the computations of Lemma 2.3

d:=35;
p:=37; // The fixed prime p.

U<x>:=PolynomialRing(Rationals()); 
K<a>:=NumberField(x^2-d);
OK:=Integers(K);

// A list of primes of multiplicative reduction for E_{a,b,c,p}. 
// Increasing the range of n enlarges this set.

qs:= [ n*p+1: n in [1..200] | (IsPrime(n*p+1)) and (IsSplit(n*p+1,OK)) and  ( (Integers() ! (Resultant(x^n-1,(x+1)^n-1)) mod (n*p+1)) ne 0  ) ];
qs;


