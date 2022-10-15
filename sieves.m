// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is included within this file

// This code carries out the sieving checks in Section 4 of the paper
// The file includes two sieves, one for X_0(61) and one for X_0(43)

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// Sieve for X_0(61)

Y:=SmallModularCurve(61);
dim:=Rank(CoordinateRing(Y));
j:=jFunction(Y,61);
Cusps:=Poles(j);

AS<x,y,z,t>:=AmbientSpace(Y);
R:=CoordinateRing(AS);
assert Rank(R) eq dim;

// We construct the numerator and denominator of the j-map so that we can apply a coordinate change afterwards.

num1:=Numerator(FunctionField(AS)!j);
denom1:=Denominator(FunctionField(AS)!j);
num2:=Evaluate(num1,[R.i : i in [1..(dim-1)]]);
denom2:=Evaluate(denom1,[R.i : i in [1..(dim-1)]]);
deg:=Max([Degree(num2),Degree(denom2)]);
num:=Homogenization(num2,R.dim,deg);
denom:=Homogenization(denom2,R.dim,deg);

////////////////

w61:=AtkinLehnerInvolution(Y,61,61);
eqns:=Equations(Y);

Mw:=Transpose((Matrix(w61)));
Diag,T:=PrimaryRationalForm(Mw);   // T^{-1} is the matrix we use for our change of coordinates.
// We choose the following T (PrimaryRationalForm can produce different diagonalising matrices on different calls)
T := ChangeRing(Matrix([[0,0,0,1],[0,1,0,0],[1,0,1,0],[-1,0,1,0]],Rationals());
assert T*Mw*(T^-1) eq Diag;

Eqg := [&+[(T^-1)[i][j]*R.j : j in [1..dim]] : i in [1..dim]];
gg:=hom<R->R | Eqg>;    // change of coordinate map.

Eqh := [&+[(T)[i][j]*R.j : j in [1..dim]] : i in [1..dim]]; // inverse of the change of coordinate map.

gnum:=gg(num);          // Change of coordinate map applied to the numerator and denominator of the j-map
gdenom:=gg(denom);

Neqns := [4*gg(e) : e in eqns];
// [4*y^2 + 4*x*z - z^2 + t^2, 4*x^3 - 4*x^2*y + 8*x^2*z + 4*x*y*z - 7*x*z^2 - 4*y*z^2 + z^3 + 3*x*t^2 - z*t^2]

NX:=Curve(ProjectiveSpace(R),Neqns);     // New Model.
YtoNX:=iso<Y -> NX | Eqh,Eqg>;           // Isomorphism from the old model to the new model.

EqNw:=[Diag[i][i]*R.i : i in [1..dim]];
Nw:=iso<NX -> NX | EqNw,EqNw>;           // New equations for diagonalised Atkin Lehner involution

// We now constuct the elliptic curve X_0^+(61) and the map to it from X_0(61)

S<r,s,u>:=PolynomialRing(Rationals(),3);
G:= r^3 - r^2*s - 3*r*s^2 - r^2*u + r*s*u + s^2*u - s*u^2;
C:= Curve(ProjectiveSpace(S), [G]);
rho:=map<NX -> C | [x,y,z]>;

EC,mu:= EllipticCurve(C, C ! [0,1,0]);
E,pi:= SimplifiedModel(EC);
Nphi:=Expand(rho*mu*pi);
Nphis:=DefiningEquations(Nphi);

///////////////////////////////////////

d:= 61;                     // Choice of d
F:= -4*y^2 - 4*x*z + z^2;

// We now apply the sieve

mls:=[* *];
Nls:=[];
ls:=[5,7,11,13,17];  // Choice of primes.

for l in ls do
    print "Considering l =", l;
    Fl:=GF(l);
    S<b>:=PolynomialRing(Fl);

    // We reduce the curves and j-map mod l.

    NXl:=ChangeRing(NX,Fl);
    ASNXl<x_0,y_0,z_0,t_0>:=AmbientSpace(NXl);
    TT:=PolynomialRing(Fl,dim);
    numl:= TT ! gnum;
    denoml:= TT ! gdenom;
    KNXl:=FunctionField(NXl);
    KNXlgens:=[KNXl!(ASNXl.i/ASNXl.3) : i in [1..(dim-1)]] cat [KNXl!1];
    jmodl:=Evaluate(numl,KNXlgens)/Evaluate(denoml,KNXlgens);

    El:=ChangeRing(E,Fl);
    Nphil:=map<NXl->El | Nphis >;
    Rl:=El ! [1,0,1];  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);     // Order modulo l
    Nls:=Nls cat [Nl];

    ms:=[];
    for m in [0..Nl-1] do

        D:=Decomposition(Pullback(Nphil,Place(m*Rl)));

        if (D[1][2] eq 1) and (#D eq 1) then // point defined over extension of Fl
            P:=Eltseq(RepresentativePoint(D[1][1]));
            jlP:=[Evaluate(jmodl,D[1][1])];
            assert ( (P[1] notin Fl) or (P[2] notin Fl) or (P[3] notin Fl) );
            if P[1] notin Fl then
                x1:=1;
                y1:=P[2]/P[1];
                z1:=P[3]/P[1];
                Pairs:=[ [x1,y1,z1] ];
            end if;
            if (P[2] notin Fl) and (P[1] in Fl) then
                x1:=P[1]/P[2];
                y1:=1;
                z1:=P[3]/P[2];
                Pairs:=[ [x1,y1,z1] ];
            end if;
            if (P[3] notin Fl) and (P[1] in Fl) and (P[2] in Fl) then
                x1:=P[1]/P[3];
                y1:=P[2]/P[3];
                z1:=1;
                Pairs:=[ [x1,y1,z1] ];
            end if;
        end if;

        if (D[1][2] eq 1) and (#D eq 2) then // pair of distinct points over Fl
            P1:=Eltseq(RepresentativePoint(D[1][1]));
            P2:=Eltseq(RepresentativePoint(D[2][1]));
            jlP1:=Evaluate(jmodl,D[1][1]);
            jlP2:=Evaluate(jmodl,D[2][1]);
            jlP:=[jlP1,jlP2];
            Pairs:=[ [P1[1],P1[2],P1[3]] , [P2[1], P2[2], P2[3] ] ];
        end if;

        if (D[1][2] eq 2) then // double point over Fl
            P:=Eltseq(RepresentativePoint(D[1][1]));
            jlP:=[Evaluate(jmodl,D[1][1])];
            Pairs:=[ [P[1],P[2],P[3] ] ];
        end if;

        if #Pairs eq 1 then
            Fel := Fl ! (Evaluate(F,Pairs[1] cat [0]));
            t:=d*b^2-Fel;
            Roo:=Set([Roots(t)[i][1] : i in [1..#Roots(t)]]);
            if  Type(jlP[1]) ne Infty  and (l gt 3)  then
                Ell:=EllipticCurveWithjInvariant(jlP[1]);
                Twotors:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell)];
                if 4 notin Twotors then
                    tt:=0;
                else tt:=4;
                end if;
            else tt:=4;
            end if;
            if #Roo gt 0 and tt ge 4 then
                ms := ms cat [m];
            end if;
        end if;

        if #Pairs eq 2 then
            Fel1:=Fl ! (Evaluate(F,Pairs[1] cat [0]));
            Fel2:=Fl ! (Evaluate(F,Pairs[2] cat [0]));
            t:=d*b^2-Fel1;
            t2:=d*b^2-Fel2;
            assert t eq t2;
            Roo:=Set([Roots(t)[i][1] : i in [1..#Roots(t)]]);
            if (Type(jlP1) ne Infty) and (Type(jlP2) ne Infty) and (l gt 3) then
                Ell1:=EllipticCurveWithjInvariant(jlP1);
                Ell2:=EllipticCurveWithjInvariant(jlP2);
                Twotors1:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell1)];
                Twotors2:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell1)];
                if (4 notin Twotors1) and (4 notin Twotors2) then
                    tt:=0;
                else tt:=4;
                end if;
            else tt:=4;
            end if;
            if #Roo gt 0 and (tt ge 4) then
                ms := ms cat [m];
            end if;
        end if;
    end for;
mls:=mls cat [*ms*];
end for;

// We now apply the Chinese Remainder Theorem to try and obtain a contradiction.

print "Number of solutions at each step:";

Newms:=[* [mls[1][j]] : j in [1..#mls[1]]*];
#Newms;
for i in [2..#mls] do
    ml :=mls[i];
    Ai:=[1 : j in [1..i]];
    Ni:=[Nls[j] : j in [1..i]];
    NNewms:=[* *];
    for j in [1..#Newms] do
        u:=[* *];
        for m in ml do
            w:=Newms[j] cat [m];
            u:=u cat [*w*];
        end for;
        NNewms:=NNewms cat u;
    end for;
    Newms:=NNewms;
    Newms:=[P : P in Newms | Solution(Ai,P,Ni) ne -1];
    #Newms;
    if #Newms eq 0 then // If Newms is empty, then we have a contradiction.
        break;
    end if;
end for;

/* Output:

Considering l = 5
Considering l = 7
Considering l = 11
Considering l = 13
Considering l = 17
Number of solutions at each step:
2
2
26
104
0

*/


/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////

// Sieve for X_0(43)

Y:=SmallModularCurve(43);
dim:=Rank(CoordinateRing(Y));
j:=jFunction(Y,43);
Cusps:=Poles(j);

AS<x,y,t>:=AmbientSpace(Y);
R:=CoordinateRing(AS);
assert Rank(R) eq dim;

// We construct the numerator and denominator of the j-map so that we can apply a coordinate change afterwards.

num1:=Numerator(FunctionField(AS)!j);
denom1:=Denominator(FunctionField(AS)!j);
num2:=Evaluate(num1,[R.i : i in [1..(dim-1)]]);
denom2:=Evaluate(denom1,[R.i : i in [1..(dim-1)]]);
deg:=Max([Degree(num2),Degree(denom2)]);
num:=Homogenization(num2,R.dim,deg);
denom:=Homogenization(denom2,R.dim,deg);

////////////////

w43:=AtkinLehnerInvolution(Y,43,43);
eqns:=Equations(Y);

Mw:=Transpose((Matrix(w43)));
Diag,T:=PrimaryRationalForm(Mw);   // T^{-1} is the matrix we use for our change of coordinates.
// We choose the following T (PrimaryRationalForm can produce different diagonalising matrices on different calls)
T := ChangeRing(Matrix([[0,0,1],[0,-1,0],[-2,-1,0]]),Rationals());

assert T*Mw*(T^-1) eq Diag;

Eqg := [&+[(T^-1)[i][j]*R.j : j in [1..dim]] : i in [1..dim]]; // change of coordinate map
Eqh := [&+[(T)[i][j]*R.j : j in [1..dim]] : i in [1..dim]]; // inverse of change of coordinate map

gg:=hom<R->R | Eqg>;    // Our change of coordinate map.

gnum:=gg(num);          // Change of coordinate map applied to the numerator and denominator of the j-map
gdenom:=gg(denom);

Neqns := [gg(e) : e in eqns];

NX:=Curve(ProjectiveSpace(R),Neqns);     // New Model.
YtoNX:=iso<Y -> NX | Eqh,Eqg>;           // Isomorphism from the old model to the new model.

EqNw:=[Diag[i][i]*R.i : i in [1..dim]];
Nw:=iso<NX -> NX | EqNw,EqNw>;           // New equations for diagonalised Atkin Lehner involution

// We now constuct the elliptic curve X_0^+(61) and the map to it from X_0(61)

P112:=ProjectiveSpace(Rationals(),[1,1,2]);
G:= 64*x^4 + 48*x^3*y + 16*x^2*y^2 + 8*x*y^3 - 3*y^4 + 16*x^2*t + 8*x*y*t + 2*y^2*t + t^2;

C:= Curve(P112, [G]);
rho:=map<NX -> C | [x,y,t^2]>;
EC,mu:=EllipticCurve(C, C ! [0,1,1]);
E,pi:= SimplifiedModel(EC);
Nphi:=Expand(rho*mu*pi);
Nphis:=DefiningEquations(Nphi);

///////////////////////////////////////

d:= 74;             // Choice of d

// We set up the first elimination method to be used in the sieve.

hh:=64*x^4 + 48*x^3*y + 16*x^2*y^2 + 16*x^2*t^2 + 8*x*y^3 + 8*x*y*t^2 - 3*y^4 + 2*y^2*t^2 + t^4;
f:= 64*x^4 + 48*x^3*y + 16*x^2*y^2 + 8*x*y^3 - 3*y^4;
g:= 16*x^2+8*x*y+2*y^2;
assert hh eq 16*Equations(NX)[1];
assert f+g*t^2+t^4 eq hh;

///////////////////////////////////////

// We now apply the sieve

mls:=[* *];
Nls:=[];
ls:=[3,5,7,17,19,29,31,47,59]; // Choice of primes.

for l in ls do
    print "Considering l =", l;
    Fl:=GF(l);
    S<b>:=PolynomialRing(Fl);

    // We reduce the curves and j-map mod l.

    NXl:=ChangeRing(NX,Fl);
    assert IsNonsingular(NXl);
    ASNXl<x_0,y_0,z_0>:=AmbientSpace(NXl);
    TT:=PolynomialRing(Fl,dim);
    numl:= TT ! gnum;
    denoml:= TT ! gdenom;

    KNXl:=FunctionField(NXl);
    KNXlgens:=[KNXl!(ASNXl.i/ASNXl.3) : i in [1..(dim-1)]] cat [KNXl!1];
    jmodl:=Evaluate(numl,KNXlgens)/Evaluate(denoml,KNXlgens);

    El:=ChangeRing(E,Fl);
    assert IsNonsingular(El);
    Nphil:=map<NXl->El | Nphis >;

    Rl:=El ! [0,0,1];  // [1,0,1] Generates E(Q)
    Nl:=Order(Rl);     // Order modulo l
    Nls:=Nls cat [Nl];

    ms:=[];
    for m in [0..Nl-1] do

        D:=Decomposition(Pullback(Nphil,Place(m*Rl)));

        if (D[1][2] eq 1) and (#D eq 1) then // point defined over extension of Fl
            P:=Eltseq(RepresentativePoint(D[1][1]));
            jlP:=[Evaluate(jmodl,D[1][1])];
            assert ( (P[1] notin Fl) or (P[2] notin Fl) );
            if P[1] notin Fl then
                x1:=1;
                y1:=P[2]/P[1];
                Pairs:=[ [x1,y1] ];
            end if;
            if (P[2] notin Fl) and (P[1] in Fl) then
                x1:=P[1]/P[2];
                y1:=1;
                Pairs:=[ [x1,y1] ];
            end if;
        end if;

        if (D[1][2] eq 1) and (#D eq 2) then // pair of distinct points over Fl
            P1:=Eltseq(RepresentativePoint(D[1][1]));
            P2:=Eltseq(RepresentativePoint(D[2][1]));
            jlP1:=Evaluate(jmodl,D[1][1]);
            jlP2:=Evaluate(jmodl,D[2][1]);
            jlP:=[jlP1,jlP2];
            Pairs:=[ [P1[1],P1[2]] , [P2[1], P2[2] ] ];
        end if;

        if (D[1][2] eq 2) then // double point over Fl
            P:=Eltseq(RepresentativePoint(D[1][1]));
            jlP:=[Evaluate(jmodl,D[1][1])];
            Pairs:=[ [P[1],P[2] ] ];
        end if;

        if #Pairs eq 1 then
            fxy:=Fl ! (Evaluate(f,Pairs[1] cat [0]));
            gxy:=Fl ! (Evaluate(g,Pairs[1] cat [0]));
            t:=d^2*b^4+d*gxy*b^2+fxy;
            if  Type(jlP[1]) ne Infty  and (l gt 3) then
                Ell:=EllipticCurveWithjInvariant(jlP[1]);
                Twotors:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell)];
                if 4 notin Twotors then
                    tt:=0;
                else tt:=4;
                end if;
            else tt:=4;
            end if;

            if #Roots(t) gt 0 and tt eq 4 then
                ms := ms cat [m];
            end if;
        end if;

        if #Pairs eq 2 then
            fxy1:=Fl ! (Evaluate(f,Pairs[1] cat [0]));
            gxy1:=Fl ! (Evaluate(g,Pairs[1] cat [0]));
            fxy2:=Fl ! (Evaluate(f,Pairs[2] cat [0]));
            gxy2:=Fl ! (Evaluate(g,Pairs[2] cat [0]));
            t1:=d^2*b^4+d*gxy1*b^2+fxy1;
            t2:=d^2*b^4+d*gxy2*b^2+fxy2;
            assert t1 eq t2;

            if (Type(jlP1) ne Infty) and (Type(jlP2) ne Infty) and (l gt 3) then
                Ell1:=EllipticCurveWithjInvariant(jlP1);
                Ell2:=EllipticCurveWithjInvariant(jlP2);
                Twotors1:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell1)];
                Twotors2:=[#TwoTorsionSubgroup(EE): EE in Twists(Ell1)];

                assert Twotors1 eq Twotors2;
                if (4 notin Twotors1) and (4 notin Twotors2) then
                    tt:=0;
                else tt:=4;
                end if;
            else tt:=4;
            end if;

            if #Roots(t1) gt 0 and tt eq 4 then
                ms := ms cat [m];
            end if;
        end if;
    end for;
    mls:=mls cat [*ms*];
end for;

// We now apply the Chinese Remainder Theorem to try and obtain a contradiction.

print "Number of solutions at each step:";
Newms:=[* [mls[1][j]] : j in [1..#mls[1]]*];
#Newms;
for i in [2..#mls] do
    ml :=mls[i];
    Ai:=[1 : j in [1..i]];
    Ni:=[Nls[j] : j in [1..i]];
    NNewms:=[* *];
    for j in [1..#Newms] do
        u:=[* *];
        for m in ml do
            w:=Newms[j] cat [m];
            u:=u cat [*w*];
        end for;
        NNewms:=NNewms cat u;
    end for;
    Newms:=NNewms;
    Newms:=[P : P in Newms | Solution(Ai,P,Ni) ne -1];
    #Newms;
    if #Newms eq 0 then // If Newms is empty, then we have a contradiction.
        break;
    end if;
end for;

/* Output:

Considering l = 3
Considering l = 5
Considering l = 7
Considering l = 17
Considering l = 19
Considering l = 29
Considering l = 31
Considering l = 47
Considering l = 59
Number of solutions at each step:
5
11
22
96
480
315
56
24
0

*/
