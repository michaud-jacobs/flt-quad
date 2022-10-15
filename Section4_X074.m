// Magma code to support the calculations in the paper Fermat's Last Theorem and Modular Curves over Real Quadratic Fields.

// This code carries out the computations for the proof of Lemma 4.9.

N:=74;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());

J:=JZero(N);
dec:=Decomposition(J);

// This is the decomposition of J_0(74)
/* 
[
    Modular abelian variety 74A of dimension 2, level 2*37 and conductor 
    2^2*37^2 over Q,
    Modular abelian variety 74B of dimension 2, level 2*37 and conductor 
    2^2*37^2 over Q,
    Modular abelian variety N(37,74,1)(37A) of dimension 1, level 2*37 and 
    conductor 37 over Q,
    Modular abelian variety N(37,74,2)(37A) of dimension 1, level 2*37 and 
    conductor 37 over Q,
    Modular abelian variety N(37,74,1)(37B) of dimension 1, level 2*37 and 
    conductor 37 over Q,
    Modular abelian variety N(37,74,2)(37B) of dimension 1, level 2*37 and 
    conductor 37 over Q
]
*/

for d in dec do
    Dimension(d),  IsZeroAt(LSeries(d),1);
end for;  

// False means the abelian variety has rank 0.

/* 
2 false
2 false
1 true
1 true
1 false
1 false
*/

ff:=Newform(dec[1]);  // These are Galois Conjugacy Class Representatives
gg:=Newform(dec[2]);
hh:=Newform(dec[5]);  // Note dec[5] and dec[6] are equal

// We would like to have all the Galois conjugacy class representatives.

f1:=Newforms("74A")[1];
f2:=Newforms("74A")[2];
f3:=Newforms("74B")[1];
f4:=Newforms("74B")[2];
f5:=Newforms("37B")[1];

Nfs:=[*f1,f2,f3,f4,f5*];

ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1];

// We consider two methods:
// one works with the above cuspforms
// the other takes integral cuspforms

//////////////////////////////////////////////////////
//////////////////////////////////////////////////////
//////////////////// Method 1 ////////////////////////
//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

// This works well in the case N=74 as the coefficients we want to consider are all integral anyway.

CuspExps:=[Nfs];

for m in ALs do
    CE:=[* *];
    for f in Nfs do

        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        fK:= SK ! (RK ! f);    // May sometimes need to increase precision here to uniquely determine form
        fKm:=AtkinLehnerOperator(m,fK);
        CE:= CE cat [*fKm*];
     end for;
     CuspExps:=CuspExps cat [CE];
end for;
   
// Choose values between 1 and 4. 
// 1 = infinity 
// i = ALs[i](infinity) for i = 2,3,4.

Cusp1:=1;   
Cusp2:=3;

Col1:=[*Coefficient(f,1) : f in CuspExps[Cusp1]*];
    
if Cusp1 eq Cusp2 then 
   Col2 := [*Coefficient(f,2) : f in CuspExps[Cusp1]*];
else Col2 := [*Coefficient(f,1) : f in CuspExps[Cusp2]*];
end if;

// We can then check the rank of the matrix manually (coefficient fields don't match up).

//////////////////////////////////////////////////////
//////////////////////////////////////////////////////
//////////////////// Method 2 ////////////////////////
//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

// We seek integral bases for the abelian varieties of dimension >1.
// We search for a prime q such that the qth coefficients of the newforms of interest are all rational
// Suffices to work with f1 and f3 here.
// Need to make sure we have distinct eigenvalues at q and that corresponding Eigenspaces are 2-dimensional 

Tups:=[];
for q in PrimesInInterval(2,1000) do
    aqf1:=Coefficient(f1,q);
    aqf3:=Coefficient(f3,q);
    if Degree(MinimalPolynomial(aqf1)) eq 1 and  Degree(MinimalPolynomial(aqf3)) eq 1 then
       Tq:=HeckeOperator(S,q);
       if Dimension(Eigenspace(Tq,aqf1)) eq 2 and Dimension(Eigenspace(Tq,aqf3)) eq 2 then
          Tups:=Tups cat [<q,aqf1,aqf3>]; 
          break; // Can stop once one value works if we like
       end if;
    end if;
end for;

// The prime 2 works. The next prime that works is 1091; then 1373.

i:=1; // Prime to use is Tups[i][1].
q:=Tups[i][1];
aqf1:=Tups[i][2];
aqf3:=Tups[i][3];
Tq:=HeckeOperator(S,q);
E1:=Basis(Eigenspace(Tq,aqf1));
E2:=Basis(Eigenspace(Tq,aqf3));

B:=Basis(S);

Nfs:=[&+[E1[1][i]*B[i] : i in [1..#B]],
      &+[E1[2][i]*B[i] : i in [1..#B]],
      &+[E2[1][i]*B[i] : i in [1..#B]],
      &+[E2[2][i]*B[i] : i in [1..#B]],
      S ! (R ! f5)];


CuspExps:=[*Nfs*];

for m in ALs do
    CE:=[* *];
    for f in Nfs do
        fm:=AtkinLehnerOperator(m,f);
        CE:= CE cat [*fm*];
     end for;
     CuspExps:=CuspExps cat [*CE*];
end for;

////////////////////////////////////////////////////////////////////////   
// For an individual formal immersion matrix:
// Choose values between 1 and 4. 
// 1 = infinity 
// i = ALs[i](infinity) for i = 2,3,4.
Cusp1:=1;   
Cusp2:=3;

Col1:=[Coefficient(f,1) : f in CuspExps[Cusp1]];
if Cusp1 eq Cusp2 then 
   Col2 := [Coefficient(f,2) : f in CuspExps[Cusp1]];
else Col2 := [Coefficient(f,1) : f in CuspExps[Cusp2]];
end if;

FIM:=Transpose(Matrix([Col1,Col2]));
FIM;
Rank(FIM);  // Rank over rationals

l:=7;
Rank(RMatrixSpace(GF(l),5,2)!FIM); // Rank mod l

////////////////////////////////////////////////////////////////////////
// We can also obtain all the formal immersion matrices:

CuspPairs:=[[i,j] : i in [1..4], j in [1..4] | i le j];
Ranks:=[];
FIMs:=[];
for Cp in CuspPairs do
    Cusp1:=Cp[1];
    Cusp2:=Cp[2];
    Col1:=[Coefficient(f,1) : f in CuspExps[Cusp1]];
    if Cusp1 eq Cusp2 then 
       Col2 := [Coefficient(f,2) : f in CuspExps[Cusp1]];
    else Col2 := [Coefficient(f,1) : f in CuspExps[Cusp2]];
    end if;
    FIM:=Transpose(Matrix([Col1,Col2])); FIM;
    Rank(FIM);  // Rank over rationals
    FIMs:=FIMs cat [FIM];
    Ranks:=Ranks cat [Rank(FIM)];

    // l:=7;
    // Rank(RMatrixSpace(GF(l),5,2)!FIM); // Rank mod l
end for;


