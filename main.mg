// GLOBAL OBJECTS
// C2:=AbelianGroup([2]);


/////////////////////////////////////////////////////////////////////
// Data Structure stuff
//
// G             is the group actually used by the cohomology code.
// n             is 2|G|
// C             is the list of elements representing the conjugacy classes
// CStabilisers  is a list of stabilisers of the elements of C in order from Z/nZ^\times
// U             is the unit group of Z/n
// i             is the map from U to Z/n
// Umod2         is U modulo squares
// pi2           is the map from the unit group of Z/n to Umod2.
// Gabmod2       is G^ab/2G^ab
// F2            is the one-dimensional trivial F_2[G]-module.
// H2            is the vector space H^2(G, M).
// CMH2          is MAGMA's cohomology-module object for H^2(G, M).
// H2Marked      is the set of marked elements in H2, which are all geometric markings.
// H1            is H^1(Q(\zeta_n)/Q, \hat{G}[2])
// gensH         is ???
// M1            is the matrix representing res_C: H1\to \oplus_{g\in C} H^1(Q(\zeta_n)/Q, \hat{<g>})
// M2            is the matrix representing res_C: H2\to \oplus_{g\in C} H^1(Q(\zeta_n)/Q, \hat{<g>})
/////////////////////////////////////////////////////////////////////
BrauerDataFormat := recformat< G, n, C, CStabilisers, U, i, Umod2, pi2, Gabmod2 , F2, H2, CMH2, H2Marked, H1, gensH, M1, M2>;


/////////////////////////////////////////////////////////////////////
// Initialises data structure, and tests that the conjugacy classes
// generate G.
function InitialiseBrauerDataStructure(G,C)
    assert ncl< G | C > eq G; // verify that the conjugacy classes generate G
    n:=2*#G;
    Zn := Integers(n);
    ZZ := Integers();
    U, i := UnitGroup(Zn);
    Umod2, pi2 := ElementaryAbelianQuotient(U,2); // enough to work with this quotient, because we only consider homomorphisms to a 2-torsion group.
    CStabilisers:=[];
    for g in C do
        g_stab:=[];
        for x in U do
            if IsConjugate(R`G, g^(ZZ!i(x)), g) then Append(~g_stab,x); end if;
        end for;
        Append(~CStabilisers, sub<U|g_stab>);
    end for;
    Hismod2 := [pi2(H) : H in CStabilisers];
    gensH := &cat[[H.i : i in [1..Ngens(H)]] : H in Hismod2];
    return rec< BrauerDataFormat | G := G, C := C, CStabilisers:=CStabilisers, gensH:=gensH, n := n, U:=U, Umod2:=Umod2, pi2:=pi2>;
end function;


/////////////////////////////////////////////////////////////////////
// Functions for the Brauer algorithm
/////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////
// Given an element beta of R`H2, tests whether the element is 
// geometrically unramified.
function IsGeometricallyMarked(beta, R)
    GbetaFP, phibetaFP, psibetaFP := Extension(R`CMH2, beta);
    Gbeta, isoToPerm := PermutationGroup(GbetaFP);
    phibeta := hom< Gbeta -> R`G | [ phibetaFP((Gbeta.i) @@ isoToPerm) : i in [1..Ngens(Gbeta)] ]>;
    success:=true;
    for g in R`C do // here is where we construct the residue map at g
        _,gtilde:=HasPreimage(phibeta,g);
        ZGg:=Centraliser(R`G,g);
        for h in Generators(ZGg) do // this is what we feed the residue map
            _,htilde:=HasPreimage(phibeta,h);
            if (gtilde, htilde) ne Id(Gbeta) then
                success:=false;
                break;
            end if;
        end for;
        if not success then break; end if;
    end for;
    return success;
end function;

/////////////////////////////////////////////////////////////////////
// Assuming that R has already had computed H^2(G,C_2),
// Computes the subset that are marked.
procedure GetMarkedGeometricElements(~R)
    F2 := GF(2);
    R`F2  := TrivialModule(R`G, F2);
    R`CMH2 := CohomologyModule(R`G, R`F2);
    R`H2 := CohomologyGroup(R`CMH2, 2);
    winners:=[];
    for beta in R`H2 do        
        if IsGeometricallyMarked(beta,R) then
            Append(~winners,beta);
        end if;
    end for;
    R`H2Marked:=sub< R`H2 | winners>;
end procedure;


procedure GetGeometricPart(~R)
// {Given
// - a group G
// - a list gis of representatives of conjugacy classes of G
// - a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
// - the cohomology module CM for the trivial G-module Z/2
// - the second cohomology group H^2(G, Z/2)
// returns the geometric Brauer residue map as a matrix over GF(2). Its action on rows represents
// the map from H^2(G, Z/2) to the direct sum of Hom(H, Z/2) for H in His.}
    GetMarkedGeometricElements(~R);
    H2basis := [R`H2.i : i in [1..Dimension(R`H2Marked)]];
    vals := [];
    for chi in H2basis do
        // for each basis element of H^2(G,Z/2), first produce the corresponding central extension.
        extn, pi, iota := Extension(R`CMH2, chi);
        // if the lift of an element to the central extension, and a power of it, still remain conjugate, we record 0 and otherwise 1
        val := &cat[[IsConjugate(extn, g, g^(R`i(x @@ R`pi2))) select 1 else 0 : x in R`gensH] where g is gi@@pi : gi in R`C];
        Append(~vals, val);
    end for;
    M2 := Matrix(GF(2), #vals, #vals[1], vals);
    R`M2:=M2;
end procedure;



procedure GetAlgebraicPart(~R)
    Gabmod2, piabmod2 := ElementaryAbelianQuotient(R`G,2);
    A, phi := Dual(Gabmod2); // A is the dual of G^ab/2*G^ab, so A is Gdual[2]. phi is the pairing G^ab/2*G^ab x A --> Z/2
    H1, psi := Hom(R`Umod2,A); // this is the domain
    vals := [];
    for i := 1 to Ngens(H1) do
        val := &cat[[phi(piabmod2(gi),psi(H1.i)(x)) : x in R`gensH] : gi in R`C];
        Append(~vals,val);
    end for;
    M1 := Matrix(GF(2), #vals, #vals[1], vals);
    R`H1:=H1;
    R`M1:=M1;
end procedure;



procedure Btilde(G,C)
// {Given
// - a group G
// - a list gis of representatives of conjugacy classes of G
// - a list His of subgroups of (Z/2|G|)^* stabilizing the conjugacy classes of gis
// - the cohomology module CM for the trivial G-module Z/2
// - the second cohomology group H^2(G, Z/2)
// returns
// - the abelian group H^1((Z/2|G|)^*, Gdual[2])=Hom(_,_)
// - H^2(G, Z/2)
// - a subspace of (F_2)^n where n is the sum of F_2-dimension of the first two return values.}
    R:=InitialiseBrauerDataStructure(G,C);
    GetGeometricPart(~R);
    GetAlgebraicPart(~R);
    M := VerticalJoin(R`M1,R`M2);
    K := Kernel(M);
    d1 := NumberOfRows(R`M1);
    d2 := NumberOfRows(R`M2);
    Btilde_gens:=[<R`H1!Eltseq(v)[1..d1], R`H2!Eltseq(v)[d1+1..d2]> : v in Basis(K)];
    total_space:=Product(R`H1, R`H2);
    Btilde_group:=sub<total_space|Btilde_gens>;
end procedure;



G:=Sym(4);
C:=[G!(1,2)];
Btilde(G,C);










