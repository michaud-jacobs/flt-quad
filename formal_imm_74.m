// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is included within the file

// This code works with the modular curve X_0(74) to verify the formal immersion criterion
// presented in the paper. See Lemma 4.9

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

N:=74;
S:=CuspForms(N);
R<q>:=PowerSeriesRing(Integers());

J:=JZero(N);
dec:=Decomposition(J); // the decomposition of J_0(74)

/* Output:

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
hh:=Newform(dec[5]);
// Note dec[5] and dec[6] are the same:
assert hh eq Newform(dec[6]);

// We would like to have all the Galois conjugacy class representatives.

f1:=Newforms("74A")[1];
f2:=Newforms("74A")[2];
f3:=Newforms("74B")[1];
f4:=Newforms("74B")[2];
f5:=Newforms("37B")[1];

Nfs:=[*f1,f2,f3,f4,f5*];

ALs:=[ m : m in Divisors(N) | GCD(m,N div m) eq 1 and m gt 1]; // Atkin--Lehner indices

// By applying the AL involutions we compute the expansions at other cusps for each newform

CuspExps:=[Nfs]; // Initial list

for m in ALs do
    CE:=[* *];
    for f in Nfs do

        K:= CoefficientField(f);
        RK:= ChangeRing(R,K);
        SK:= BaseChange(S,K);
        fK:= SK ! (RK ! f);
        fKm:=AtkinLehnerOperator(m,fK);
        CE:= CE cat [*fKm*];
     end for;
     CuspExps:=CuspExps cat [CE];
end for;

// We compute the 4 formal immersion matrices, F_inf, F_inf,2, F_inf,3, and F_inf,4
// Output included after the loop

Cusp1:=1; // 1 <--> infinity,
for i in [1,2,3,4] do
    Cusp2 := i; // i <--> ALs[i](infinity) for i = 2,3,4.

    Col1:=[Integers() ! Coefficient(f,1) : f in CuspExps[Cusp1]]; // First column of matrix

    if Cusp1 eq Cusp2 then
        Col2 := [Integers() ! Coefficient(f,2) : f in CuspExps[Cusp1]]; // Second column of matrix
    else Col2 := [Integers() ! Coefficient(f,1) : f in CuspExps[Cusp2]]; // Second column of matrix
    end if;
    c1 := Transpose(Matrix([Col1]));
    c2 := Transpose(Matrix([Col2]));
    F_inf_i := HorizontalJoin(c1,c2);
    print  F_inf_i;
    print "++++++++++++++++++++";
end for;

// We see that at each matrix has rank 2 modulo q for any prime q > 2.
/* Output:

[ 1 -1]
[ 1 -1]
[ 1  1]
[ 1  1]
[ 1  0]
++++++++++++++++++++
[ 1  1]
[ 1  1]
[ 1 -1]
[ 1 -1]
[ 1  0]
++++++++++++++++++++
[ 1 -1]
[ 1 -1]
[ 1  1]
[ 1  1]
[ 1 -1]
++++++++++++++++++++
[ 1 -1]
[ 1 -1]
[ 1 -1]
[ 1 -1]
[ 1  0]
++++++++++++++++++++

*/
