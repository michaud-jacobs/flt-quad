// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

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

