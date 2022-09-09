// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

// This code carries out the computations of Proposition 6.2 in the paper. 
// When p > Discriminant we can use a variant of this (see code below).

d:=61;
p:=127; // p is an odd regular prime. 

K:=QuadraticField(d);
D:=Discriminant(Integers(K));

Snsum:=function(n,x,p);
       Sn:= (&+ [ u^n mod p : u in [0..Ceiling(x)-1]]) mod p;
       return Sn;
end function;

AjD:=function(j,p)
     A:=  [ KroneckerSymbol(D,t) mod p: t in [1..D] | IsZero( (t-j*D) mod p)];
     if #A eq 0 then 
        AA:=0;
     else AA:=&+A;
     end if;
     return AA;
end function;

ntotest:=[n : n in [1..p-1] | IsOdd(n)];
modp:=[];

for n in ntotest do
    Main:= (&+[  Snsum(n,j,p) * (AjD(j,p) )  mod p   : j in [1..p] ]) mod p;
    modp:= modp cat [Main mod p];
end for;

0 in modp; // False if an only if p is d-regular.

///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

// This code works faster if p > Discriminant.

d:=55;
p:=271; // p is an odd regular prime. 

K:=QuadraticField(d);
D:=Discriminant(Integers(K));

assert p gt D; // Method holds for p > Discriminant.

Snsum:=function(n,x);
       Sn:=&+ [ u^n : u in [0..Ceiling(x)-1]];
       return Sn;
end function;


ntotest:=[n : n in [1..p-1] | IsOdd(n)];
modp:=[];

for n in ntotest do
     
    Main:= &+[Snsum(n,(j*p)/D) * (KroneckerSymbol(D,j)) : j in [1..Floor((D-1)/2)]];
    modp:= modp cat [Main mod p];
end for;

0 in modp;  // False if an only if p is d-regular.
