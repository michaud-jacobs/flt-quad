// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is included within the file

// This code includes functions to check if a given prime p is d-regular
// It uses the methods of Section 6 of the paper

// The main function, is_regular, verifies whether or not a prime p < 1000 is d-regular

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// Irregular primes < 1000
irregular_p := [37, 59, 67, 101, 103, 131, 149, 157, 233, 257, 263, 271, 283, 293, 307, 311, 347, 353, 379, 389, 401, 409, 421, 433, 461, 463, 467, 491, 523, 541, 547, 557, 577, 587, 593, 607, 613, 617, 619, 631, 647, 653, 659, 673, 677, 683, 691, 727, 751, 757, 761, 773, 797, 809, 811, 821, 827, 839, 877, 881, 887, 929, 953, 971];

// auxiliary function

Snsum_1:=function(n,x,p);
       Sn:= (&+ [ u^n mod p : u in [0..Ceiling(x)-1]]) mod p;
       return Sn;
end function;

// auxiliary function

AjD:=function(j,p, D)
     A:=  [ KroneckerSymbol(D,t) mod p: t in [1..D] | IsZero( (t-j*D) mod p)];
     if #A eq 0 then
        AA:=0;
     else AA:=&+A;
     end if;
     return AA;
end function;

// This function verifies whether a prime p < 1000, with p not dividing d, is d-regular or not
// If p > Discriminat(K), where K = Q(sqrt_d) then the next function, is_regular_big, is faster

is_regular_small := function(d,p);
    assert p lt 1000;
    assert p gt 2;
    assert IsZero(d mod p) eq false;
    if p in irregular_p then
        return false;
    end if;
    K:=QuadraticField(d);
    D:=Discriminant(Integers(K));
    ntotest:=[n : n in [1..p-1] | IsOdd(n)];
    modp:=[];
    for n in ntotest do
        Main:= (&+[  Snsum_1(n,j,p) * (AjD(j,p,D) )  mod p   : j in [1..p] ]) mod p;
        modp:= modp cat [Main mod p];
    end for;

    if 0 in modp then // False if an only if p is d-regular.
        return false; // p is not d-regular
    else return true;
    end if;
end function;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// auxiliary function

Snsum_2:=function(n,x);
       Sn:=&+ [ u^n : u in [0..Ceiling(x)-1]];
       return Sn;
end function;

// This function also verifies if p is d-regular.
// It is faster than is_regular_small if p > Discriminant(Q(sqrt_d))

is_regular_big := function(d,p);
    assert p lt 1000;
    assert p gt 2;
    assert IsZero(d mod p) eq false;
    K:=QuadraticField(d);
    D:=Discriminant(Integers(K));
    assert p gt D;
    if p in irregular_p then
        return false;
    end if;
    K:=QuadraticField(d);
    D:=Discriminant(Integers(K));

    ntotest:=[n : n in [1..p-1] | IsOdd(n)];
    modp:=[];

    for n in ntotest do
        Main:= &+[Snsum_2(n,(j*p)/D) * (KroneckerSymbol(D,j)) : j in [1..Floor((D-1)/2)]];
        modp:= modp cat [Main mod p];
    end for;

    if 0 in modp then // False if an only if p is d-regular.
        return false; // p is not d-regular
    else return true;
    end if;
end function;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// This functions checks whether p is d-regular
// It combines the functions is_regular_small and is_regular_big to do this.

is_regular := function(d,p);
    K:=QuadraticField(d);
    D:=Discriminant(Integers(K));
    if p le D then
        tf := is_regular_small(d,p);
    else
        tf := is_regular_big(d,p);
    end if;
    return tf;
end function;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

// We verify our function produces the same data as that computed by Hao and Parry

// The following primes are the 2- and 5- irregular primes given by Hao and Parry
// The lists do not include all Q-irregular primes

HP_2 := [11,13,19,31,37,59,71,79,89,107,127,149,151,173,179,199];
HP_5 := [17,19,41,61,67,73,107,127,131,137,139,149,151,163,167,191];

// This loop ensures our functions produce the same data

for d in [2,5] do
    irreg_p_d := [];
    for p in PrimesInInterval(9,200) do
        tf := is_regular(d,p);
        if p lt 50 then
            assert is_regular_small(d,p) eq is_regular_big(d,p); // sanity check
        end if;
        if tf eq false then
            irreg_p_d := irreg_p_d cat [p];
        end if;
    end for;
    print "Irregular primes for d =", d, "are:", irreg_p_d;
    irreg_200 := [p : p in irregular_p | p lt 200];
    if d eq 2 then
        assert Set(HP_2 cat irreg_200) eq Set(irreg_p_d);
    else
        assert Set(HP_5 cat irreg_200) eq Set(irreg_p_d);
    end if;
end for;

/* Output:

Irregular primes for d = 2 are: [ 11, 13, 19, 31, 37, 59, 67, 71, 79, 89, 101,
103, 107, 127, 131, 149, 151, 157, 173, 179, 199 ]
Irregular primes for d = 5 are: [ 17, 19, 37, 41, 59, 61, 67, 73, 101, 103, 107,
127, 131, 137, 139, 149, 151, 157, 163, 167, 191 ]

*/

// We verify that some of the primes we would like to eliminate are d-irregular
// So we cannot eliminate them using these methods

assert is_regular(34,23) eq false;
assert is_regular(55,23) eq false;
assert is_regular(97,17) eq false;
assert is_regular(86,31) eq false;
