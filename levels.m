// Magma code to support the computations in the paper
// Fermat's Last Theorem and modular curves over real quadratic fields by Philippe Michaud-Jacobs.
// See https://github.com/michaud-jacobs/flt-quad for all the code files and links to the paper

// The code works on Magma V2.26-10
// The output is in the levels_output.txt file

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// Input: Squarefree d > 0
// Output:
// List of possibilities for the level-lowered levels N_p, sorted by norm
// The quadratic field K = Q(sqrt_d)
// Set S of prime ideals in K above 2
// Set H of representatives for Cl(K) / Cl(K)^2

Np_possibilities := function(d);
    T<x>:=PolynomialRing(Rationals());
    K<sqrt_d>:=NumberField(x^2-d);
    OK:=RingOfIntegers(K);
    ClK,mu:=ClassGroup(K);
    muinv:=mu^(-1);
    Fac_2:=Factorisation(2*OK);
    S:=[Fac_2[i][1] : i in [1..#Fac_2]]; // The set S of primes above 2.
    QuoClK,nu:=quo<ClK | 2*ClK>;
    elts:=[q : q in QuoClK];
    H:=[1*OK];
    for i in [2..#QuoClK] do
        primes := [P : P in PrimesUpTo(40,K) | IsOdd(Norm(P)) and nu(muinv(P)) eq elts[i]];
        _,n:=Minimum([Norm(P) : P in primes]);
        H_i:=primes[n];
        if d eq 65 then
            H_i := primes[n+1]; // We choose a different prime in the case d = 65
        end if;
        H:=H cat [H_i];
    end for;              // H forms a set of representatives for Cl(K)/Cl(K)^2, with #H=r.

    // We now follow Freitas and Siksek's strategy to calculate a list of possible levels N_p.
    // We first compute possibilities for the even part of the level.

    R<y>:=PolynomialRing(K);
    rams:=[Fac_2[i][2] : i in [1..#Fac_2]];
    b:=&*[(S[i])^(2*rams[i]+1) : i in [1..#Fac_2]];  // b is as in Freitas and Siksek's paper
    OKb,pi:=quo<OK | b>;
    U,t:=UnitGroup(OKb);
    s:=t^(-1);

    Sq:={oo^2 : oo in OKb | IsUnit(oo)};
    SFU,w:=quo<U |s(Sq)>;

    Uni,psi:=UnitGroup(OK);
    UniGens:=SetToIndexedSet(Generators(Uni));
    imphi:=[pi(psi(gg)): gg in UniGens | IsUnit(pi(psi(gg)))];
    Coker, v := quo<SFU | w(s(imphi))>;
    reps:=[(t(  (cc @@ v   ) @@ w)) @@ pi : cc in Coker];

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
            for k in [1..#S] do
                if IsIrreducible(rootlam) eq true then
                    L := NumberField(rootlam);
                    OL:=RingOfIntegers(L);
                    D:=Discriminant(OL);
                    v:=Valuation(D, S[k]);
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
            Npeven:=&*[S[j]^(exps[j]): j in [1..#S]];
            Npevensi:=Npevensi cat [Npeven];
        end for;
        _,pos:=Minimum([Norm(n): n in Npevensi]);
        newreps:=newreps cat [Lambdas[i][pos]];
        Npevens:=Npevens cat [Npevensi[pos]];
    end for;
    newrepsK:=[K ! (OK ! newreps[i]) : i in [1..#newreps]];
    Vals:= [   [Valuation(Npevens[i],S[j]) : i in [1..#reps]]   : j in [1..#S]];

    Npevset:=IndexedSet(Npevens); // Possibilities for the even part of N_p, when 2 is not inert in K.

    if IsInert(2,OK) eq true then
        Npevset:= Npevset join {S[1]^4};
    end if;

    // Combine even and odd part of N_p to give a list of possibilities for N_p.

    N_ps:={};
    for i in [1..#H] do
        for j in [1..#Npevset] do
            Np:=((H[i])^2)*(Npevset[j]);
            N_ps:=N_ps join {Np};
        end for;
    end for;
    N_ps:=Sort(IndexedSet(N_ps));   // A list of the possible levels N_p, ordered by norm
    return N_ps, K, S, H;
end function;

// We now list the possible levels N_p for each d
// We also list the dimensions of the spaces of modular forms and newforms
// See the output file levels_output.txt as well as the table in the appendix of the paper.
// We include data for 1 < d < 25 to check against Freitas and Siksek's paper.

for d in [d : d in [2..100] | IsSquarefree(d)] do
    print "Computing the possible levels N_p for d =", d;
    N_ps, K, S, H := Np_possibilities(d);
    if #S eq 2 then
        print "2 splits in K and S = {p_1, p_2}";
    else if Norm(S[1]) eq 2 then
             print "2 is ramified in K and S = {p}";
         else print "2 is inert in K and S = {p = 2O}";
         end if;
    end if;
    r := #H;
    print "Cl(K) / Cl(K)^2 has size r =", r;
    if r eq 2 then
        m := H[2];
        m_gens := [K ! gg : gg in Generators(m)];
        printf "The ideal m is generated by %o and %o \n", m_gens[1], m_gens[2];
    else print "The ideal m is generated by 1";
    end if;
    print "Possible levels N_p are:", [Factorisation(np) : np in N_ps];
    for Np in N_ps do
        M := HilbertCuspForms(K, Np);
        NewM:=NewSubspace(M);
        print "Dimension of space of modular forms n =", Dimension(M);
        print "Dimension of space of newforms n_new =", Dimension(NewM);
        print "=======";
    end for;
    print "++++++++++++++++++++++++++++++++++++++++++++++++++";
end for;
