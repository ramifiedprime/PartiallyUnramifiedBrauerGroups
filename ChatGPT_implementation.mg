// PRB_reference_H1Ghat2.mg
//
// Small reference implementation for the Q-case, 2-primary partially ramified
// Brauer-pair computation.
//
// This version deliberately puts the algebraic component in
//     H^1(U_2, Ghat[2])
// rather than H^1(U_2, Ghat[2^infty]).  Thus it DOES NOT quotient by the
// discrepancy coming from higher 2-power characters; the user can handle that
// separately by hand.
//
// It is intentionally brute-force and explicit.  It is meant to be easy to
// audit, not fast.
//
// Main entry point:
//     R := PartiallyRamifiedBrauerPairs(G, Creps);
//
// Output pairs are triples
//     <geo_coords, alg_index, marking_shifts>
// where
//     geo_coords      are F_2-coordinates in R`GeometricBasisH2;
//     alg_index       indexes R`AlgebraicH1Classes;
//     marking_shifts  is a witness for the lifted marking.
//
// Recover data:
//     Ext := PRBExactSequence(R, P);
//     D   := PRBMarkedClasses(R, P);
//     a   := PRBAlgebraicCocycle(R, P);

// ============================================================================
// Basic utilities
// ============================================================================

function IsTwoPower(n)
    if n le 0 then return false; end if;
    while (n mod 2) eq 0 do n div:= 2; end while;
    return n eq 1;
end function;

function TwoPart(n)
    m := 1;
    while (n mod 2) eq 0 do
        m *:= 2;
        n div:= 2;
    end while;
    return m;
end function;

function TwoPartExponent(G)
    e := 1;
    for g in G do e := LCM(e, Order(g)); end for;
    return TwoPart(e);
end function;

function UnitMul(a,b,N)
    r := (a*b) mod N;
    if r eq 0 then r := N; end if;
    return r;
end function;

function UnitInv(a,N)
    aa := a mod N;
    for b in [1..N] do
        if GCD(b,N) eq 1 and ((aa*b-1) mod N) eq 0 then
            return b;
        end if;
    end for;
    error "UnitInv: not a unit";
end function;

function UnitOrder(a,N)
    if GCD(a,N) ne 1 then error "UnitOrder: not a unit"; end if;
    x := a mod N;
    if x eq 0 then x := N; end if;
    y := x; o := 1;
    while y ne 1 do
        y := (y*x) mod N;
        o +:= 1;
    end while;
    return o;
end function;

function UnitClosure(gens,N)
    S := {1};
    changed := true;
    while changed do
        changed := false;
        T := S;
        for x in S do
            for g in gens do
                y := UnitMul(x,g,N);
                if not (y in T) then
                    Include(~T,y); changed := true;
                end if;
            end for;
        end for;
        S := T;
    end while;
    return S;
end function;

function GreedyUnitGenerators(U,N)
    gens := [];
    S := {1};
    for u in U do
        if not (u in S) then
            Append(~gens,u);
            S := UnitClosure(gens,N);
        end if;
        if #S eq #U then break; end if;
    end for;
    return gens;
end function;

function AllBits(n)
    if n eq 0 then return [ [] ]; end if;
    return [ [ ((m div 2^(i-1)) mod 2) : i in [1..n] ] : m in [0..2^n-1] ];
end function;

function SeqKey(S)
    return Sprint(S);
end function;

function Vec0(n)
    return [ 0 : i in [1..n] ];
end function;

function AddMod(a,b,M)
    return [ (a[i]+b[i]) mod M : i in [1..#a] ];
end function;

function NegMod(a,M)
    return [ (-a[i]) mod M : i in [1..#a] ];
end function;

function ScalarMod(c,a,M)
    return [ ((c mod M)*a[i]) mod M : i in [1..#a] ];
end function;

function BitOfModuleElt(v)
    return (Integers()!Eltseq(v)[1]) mod 2;
end function;

function BitSeq(v)
    return [ (Integers()!x) mod 2 : x in Eltseq(v) ];
end function;

function F2Generators(H)
    return [ H.i : i in [1..Ngens(H)] | H.i ne H!0 ];
end function;

function F2LinearCombination(H, basis, coeffs)
    s := H!0;
    for i in [1..#basis] do
        if coeffs[i] mod 2 eq 1 then s +:= basis[i]; end if;
    end for;
    return s;
end function;

function ClassSet(G,g)
    return { x^-1*g*x : x in G };
end function;

function ClassPower(C,k)
    return { x^k : x in C };
end function;

function ClassIndex(Csets,C)
    for i in [1..#Csets] do
        if C eq Csets[i] then return i; end if;
    end for;
    return 0;
end function;

// ============================================================================
// Input, U_2, and residue rows
// ============================================================================

function CleanC(G, Creps)
    reps := [];
    csets := [];
    e := Identity(G);
    for g in Creps do
        if g eq e then continue; end if;
        C := ClassSet(G,g);
        if &and[ C ne D : D in csets ] then
            Append(~reps,g); Append(~csets,C);
        end if;
    end for;
    return reps, csets;
end function;

function ValidateC(G, Creps, Csets)
    if #Creps eq 0 then return false, "C is empty after removing identity."; end if;

    X := {};
    for C in Csets do X := X join C; end for;
    if sub< G | [x : x in X] > ne G then
        return false, "The union of C does not generate G.";
    end if;

    for i in [1..#Csets] do
        for k in [1..#G] do
            if GCD(k,#G) eq 1 then
                if ClassIndex(Csets, ClassPower(Csets[i],k)) eq 0 then
                    return false, Sprintf("C is not closed under invertible power %o.", k);
                end if;
            end if;
        end for;
    end for;

    return true, "ok";
end function;

function U2Data(N)
    U := [ a : a in [1..N] | GCD(a,N) eq 1 ];
    U2 := [ a : a in U | IsTwoPower(UnitOrder(a,N)) ];
    gens := GreedyUnitGenerators(U2,N);
    return U2, gens;
end function;

function ResidueRows(Csets,U2)
    rows := [];
    for i in [1..#Csets] do
        for k in U2 do
            j := ClassIndex(Csets, ClassPower(Csets[i],k));
            if j eq 0 then error "ResidueRows: C not U2-stable"; end if;
            Append(~rows,<i,k,j>);
        end for;
    end for;
    return rows;
end function;

// ============================================================================
// Geometric side
// ============================================================================

function TrivialF2CM(G)
    F := GF(2);
    mats := [ IdentityMatrix(F,1) : i in [1..Ngens(G)] ];
    return CohomologyModule(G, GModule(G,mats));
end function;

function NormalizedTwoCocycleBit(CM, h2, G)
    t := TwoCocycle(CM,h2);
    e := Identity(G);
    c := BitOfModuleElt(t(<e,e>));

    return function(g,h)
        // Add the coboundary of the 1-cochain s with s(e)=t(e,e), s(x)=0 otherwise.
        sg  := (g eq e) select c else 0;
        sh  := (h eq e) select c else 0;
        sgh := (g*h eq e) select c else 0;
        return (BitOfModuleElt(t(<g,h>)) + sg + sh + sgh) mod 2;
    end function;
end function;

function GeometricKernel(G,Creps,CM)
    F := GF(2);
    H2 := CohomologyGroup(CM,2);
    H2bas := F2Generators(H2);
    f := [ NormalizedTwoCocycleBit(CM,b,G) : b in H2bas ];

    nrows := &+[ Ngens(Centralizer(G,g)) : g in Creps ];
    A := ZeroMatrix(F,nrows,#H2bas);
    r := 0;
    for g in Creps do
        Z := Centralizer(G,g);
        for ell in [1..Ngens(Z)] do
            h := Z.ell; r +:= 1;
            for j in [1..#H2bas] do
                A[r,j] := F!((f[j](g,h)+f[j](h,g)) mod 2);
            end for;
        end for;
    end for;

    K := Nullspace(Transpose(A));
    Kcoords := [ BitSeq(v) : v in Basis(K) ];
    Kbas := [ F2LinearCombination(H2,H2bas,c) : c in Kcoords ];

    return H2, H2bas, A, Kcoords, Kbas;
end function;

function CentralExtensionFromH2(G,CM,h2)
    f := NormalizedTwoCocycleBit(CM,h2,G);
    Gelts := [g : g in G];
    pos := AssociativeArray();
    for i in [1..#Gelts] do pos[Gelts[i]] := i; end for;
    n := #Gelts; e := Identity(G);

    function PairIndex(a,g)
        return (a mod 2)*n + pos[g];
    end function;

    function IndexPair(p)
        a := (p-1) div n;
        i := ((p-1) mod n) + 1;
        return a, Gelts[i];
    end function;

    S := Sym(2*n);
    function L(a,g)
        imgs := [];
        for p in [1..2*n] do
            b,h := IndexPair(p);
            Append(~imgs, PairIndex((a+b+f(g,h)) mod 2, g*h));
        end for;
        return S!imgs;
    end function;

    E := sub< S | [L(1,e)] cat [ L(0,G.i) : i in [1..Ngens(G)] ] >;
    z := E!L(1,e);

    function Lift(g)
        return E!L(0,g);
    end function;

    function Projection(x)
        p := PairIndex(0,e)^x;
        a,g := IndexPair(p);
        return g;
    end function;

    RF := recformat< E, z, Lift, Projection, CocycleBit >;
    return rec< RF | E:=E, z:=z, Lift:=Lift, Projection:=Projection, CocycleBit:=f >;
end function;

function BaseGeomBits(Creps,Rows,Ext)
    E := Ext`E; z := Ext`z; L := Ext`Lift;
    bits := [];
    for row in Rows do
        i := row[1]; k := row[2]; j := row[3];
        lhs := L(Creps[i])^k;
        rhs := L(Creps[j]);
        if IsConjugate(E,lhs,rhs) then
            Append(~bits,0);
        elif IsConjugate(E,lhs,z*rhs) then
            Append(~bits,1);
        else
            error Sprintf("Bad lifted transition %o --%o--> %o",i,k,j);
        end if;
    end for;
    return bits;
end function;

function ShiftBits(bits,Rows,shifts)
    return [ (bits[r] + shifts[Rows[r][1]] + shifts[Rows[r][3]]) mod 2 : r in [1..#Rows] ];
end function;

function GeometricResidues(G,Creps,CM,H2,Kbas,Rows,M)
    // Return triples <coordinates in Kbas, marking shifts, residue vector in Z/MZ>.
    out := [];
    half := M div 2;
    for c in AllBits(#Kbas) do
        h2 := F2LinearCombination(H2,Kbas,c);
        Ext := CentralExtensionFromH2(G,CM,h2);
        b0 := BaseGeomBits(Creps,Rows,Ext);
        for s in AllBits(#Creps) do
            b := ShiftBits(b0,Rows,s);
            Append(~out,<c,s,[ (half*x) mod M : x in b ]>);
        end for;
    end for;
    return out;
end function;

// ============================================================================
// Algebraic side: H^1(U_2, Hom(G,Z/2Z))
// ============================================================================

function HomGtoZM(G,M)
    Gelts := [g : g in G];
    Gpos := AssociativeArray();
    for i in [1..#Gelts] do Gpos[Gelts[i]] := i; end for;
    gens := [G.i : i in [1..Ngens(G)]];

    if M eq 1 or #gens eq 0 then
        return [ Vec0(#Gelts) ], Gelts, Gpos;
    end if;

    choices := [ [a : a in [0..M-1] | (Order(gens[i])*a) mod M eq 0] : i in [1..#gens] ];

    function TryExtend(vals)
        A := AssociativeArray();
        e := Identity(G);
        A[e] := 0;
        for i in [1..#gens] do
            if IsDefined(A,gens[i]) and A[gens[i]] ne vals[i] mod M then
                return false, [];
            end if;
            A[gens[i]] := vals[i] mod M;
        end for;

        stepG := [];
        stepV := [];
        for i in [1..#gens] do
            Append(~stepG, gens[i]);    Append(~stepV, vals[i] mod M);
            Append(~stepG, gens[i]^-1); Append(~stepV, (-vals[i]) mod M);
        end for;

        queue := [e]; head := 1;
        while head le #queue do
            x := queue[head]; head +:= 1;
            vx := A[x];
            for t in [1..#stepG] do
                y := x*stepG[t];
                vy := (vx+stepV[t]) mod M;
                if IsDefined(A,y) then
                    if A[y] ne vy then return false, []; end if;
                else
                    A[y] := vy; Append(~queue,y);
                end if;
            end for;
        end while;

        return true, [ A[g] mod M : g in Gelts ];
    end function;

    chars := [];
    seen := AssociativeArray();

    procedure Recurse(i,vals,~chars,~seen)
        if i gt #gens then
            ok,ch := TryExtend(vals);
            if ok then
                key := SeqKey(ch);
                if not IsDefined(seen,key) then seen[key]:=true; Append(~chars,ch); end if;
            end if;
            return;
        end if;
        for a in choices[i] do Recurse(i+1, vals cat [a], ~chars, ~seen); end for;
    end procedure;

    Recurse(1,[],~chars,~seen);
    return chars, Gelts, Gpos;
end function;

function ExtendU2Cocycle(U2,Ugens,N,M,A,genVals)
    nA := #A[1];
    f := AssociativeArray();
    f[1] := Vec0(nA);

    stepU := [];
    stepV := [];
    for i in [1..#Ugens] do
        u := Ugens[i];
        v := genVals[i];
        Append(~stepU,u); Append(~stepV,v);
        ui := UnitInv(u,N);
        // f(u^-1) = u^-1 * (-f(u))
        Append(~stepU,ui); Append(~stepV, ScalarMod(ui,NegMod(v,M),M));
    end for;

    queue := [1]; head := 1;
    while head le #queue do
        x := queue[head]; head +:= 1;
        fx := f[x];
        for t in [1..#stepU] do
            u := stepU[t];
            y := UnitMul(x,u,N);
            // f(xu) = f(x) + x f(u)
            fy := AddMod(fx, ScalarMod(x,stepV[t],M), M);
            if IsDefined(f,y) then
                if f[y] ne fy then return false, []; end if;
            else
                f[y] := fy; Append(~queue,y);
            end if;
        end for;
    end while;

    return true, [ f[u] : u in U2 ];
end function;

function U2Cocycles(U2,Ugens,N,M,A)
    if #Ugens eq 0 then return [ [ Vec0(#A[1]) ] ]; end if;
    Z := [];
    seen := AssociativeArray();

    procedure Recurse(i,vals,~Z,~seen)
        if i gt #Ugens then
            ok,coc := ExtendU2Cocycle(U2,Ugens,N,M,A,vals);
            if ok then
                key := SeqKey(coc);
                if not IsDefined(seen,key) then seen[key]:=true; Append(~Z,coc); end if;
            end if;
            return;
        end if;
        for a in A do Recurse(i+1, vals cat [a], ~Z, ~seen); end for;
    end procedure;

    Recurse(1,[],~Z,~seen);
    return Z;
end function;

function U2Coboundaries(U2,M,A)
    B := [];
    seen := AssociativeArray();
    for a in A do
        b := [ ScalarMod(u-1,a,M) : u in U2 ];
        key := SeqKey(b);
        if not IsDefined(seen,key) then seen[key]:=true; Append(~B,b); end if;
    end for;
    return B;
end function;

function AddCocycles(c,b,M)
    return [ AddMod(c[i],b[i],M) : i in [1..#c] ];
end function;

function AlgebraicH1_Ghat2(G,Creps,U2,Ugens,N,Rows)
    M := 2;
    A, Gelts, Gpos := HomGtoZM(G,M);
    Z1 := U2Cocycles(U2,Ugens,N,M,A);
    B1 := U2Coboundaries(U2,M,A);

    Upos := AssociativeArray();
    for i in [1..#U2] do Upos[U2[i]] := i; end for;

    used := AssociativeArray();
    classes := [];
    for z in Z1 do
        if IsDefined(used,SeqKey(z)) then continue; end if;
        for b in B1 do used[SeqKey(AddCocycles(z,b,M))] := true; end for;
        Append(~classes,z);
    end for;

    residues := [];
    for z in classes do
        res := [];
        for row in Rows do
            i := row[1]; k := row[2];
            chi := z[Upos[k]];
            Append(~res, chi[Gpos[Creps[i]]] mod M);
        end for;
        Append(~residues,res);
    end for;

    return A, Gelts, Gpos, Z1, B1, classes, residues;
end function;

// ============================================================================
// Matching and main function
// ============================================================================

function MatchPairs(Geo,AlgResidues)
    pairs := [];
    seen := AssociativeArray();
    for x in Geo do
        coords := x[1]; shifts := x[2]; gres := x[3];
        for a in [1..#AlgResidues] do
            if gres eq AlgResidues[a] then
                // Marking shifts are witnesses, not extra Brauer elements.
                key := Sprint(<coords,a>);
                if not IsDefined(seen,key) then
                    seen[key] := true;
                    Append(~pairs,<coords,a,shifts>);
                end if;
            end if;
        end for;
    end for;
    return pairs;
end function;

function PartiallyRamifiedBrauerPairs(G, Creps : CheckInput:=true)
    RF := recformat<
        Ok, Message, G, OriginalCRepresentatives, CRepresentatives, Csets,
        Modulus, U2, U2Generators, Rows, CM,
        H2, H2Basis, GeometricResidueMatrix, GeometricKernelCoords,
        GeometricBasisH2, GeometricResidues,
        AlgebraicModulus, GhatElements, AlgebraicZ1, AlgebraicB1,
        AlgebraicH1Classes, AlgebraicResidues,
        MatchingPairs
    >;

    reps,csets := CleanC(G,Creps);
    N := 2*#G;
    U2,Ugens := U2Data(N);

    if (#G mod 2) eq 1 then
        return rec< RF | Ok:=true, Message:="Odd order: no 2-primary data.",
                         G:=G, OriginalCRepresentatives:=Creps,
                         CRepresentatives:=reps, Csets:=csets,
                         Modulus:=N, U2:=U2, U2Generators:=Ugens,
                         MatchingPairs:=[<[],1,[]>] >;
    end if;

    if CheckInput then
        ok,msg := ValidateC(G,reps,csets);
        if not ok then
            return rec< RF | Ok:=false, Message:=msg, G:=G,
                             OriginalCRepresentatives:=Creps,
                             CRepresentatives:=reps, Csets:=csets,
                             Modulus:=N, U2:=U2, U2Generators:=Ugens >;
        end if;
    end if;

    rows := ResidueRows(csets,U2);
    M := 2;   // algebraic target is Ghat[2], and geometric residues are F_2-valued

    CM := TrivialF2CM(G);
    H2,H2bas,Gmat,Kcoords,Kbas := GeometricKernel(G,reps,CM);
    Geo := GeometricResidues(G,reps,CM,H2,Kbas,rows,M);

    A,Gelts,Gpos,Z1,B1,H1,resA := AlgebraicH1_Ghat2(G,reps,U2,Ugens,N,rows);
    pairs := MatchPairs(Geo,resA);

    return rec< RF |
        Ok:=true, Message:="ok", G:=G,
        OriginalCRepresentatives:=Creps, CRepresentatives:=reps, Csets:=csets,
        Modulus:=N, U2:=U2, U2Generators:=Ugens, Rows:=rows, CM:=CM,
        H2:=H2, H2Basis:=H2bas, GeometricResidueMatrix:=Gmat,
        GeometricKernelCoords:=Kcoords, GeometricBasisH2:=Kbas,
        GeometricResidues:=Geo,
        AlgebraicModulus:=M, GhatElements:=A, AlgebraicZ1:=Z1,
        AlgebraicB1:=B1, AlgebraicH1Classes:=H1, AlgebraicResidues:=resA,
        MatchingPairs:=pairs >;
end function;

// ============================================================================
// Recovery helpers
// ============================================================================

function PRBH2Element(R,P)
    return F2LinearCombination(R`H2,R`GeometricBasisH2,P[1]);
end function;

function PRBExactSequence(R,P)
    return CentralExtensionFromH2(R`G,R`CM,PRBH2Element(R,P));
end function;

function PRBMarkedClasses(R,P)
    Ext := PRBExactSequence(R,P);
    E := Ext`E; z := Ext`z; L := Ext`Lift;
    shifts := P[3];
    return [ ClassSet(E, (shifts[i] eq 1) select z*L(R`CRepresentatives[i]) else L(R`CRepresentatives[i]))
             : i in [1..#R`CRepresentatives] ];
end function;

function PRBAlgebraicCocycle(R,P)
    // A representative U_2 -> Hom(G,Z/2Z).  Values are character-vectors on G.
    return R`AlgebraicH1Classes[P[2]];
end function;

procedure PRBSummary(R)
    if not R`Ok then
        printf "Input failed: %o\n", R`Message;
        return;
    end if;
    printf "Status: %o\n", R`Message;
    printf "|G| = %o, modulus = %o, algebraic modulus = %o\n", #R`G, R`Modulus, R`AlgebraicModulus;
    printf "#classes in C = %o, #U2 = %o, #rows = %o\n", #R`CRepresentatives, #R`U2, #R`Rows;
    printf "dim geometric kernel = %o\n", #R`GeometricBasisH2;
    printf "|H^1(U2,Ghat[2])| = %o\n", #R`AlgebraicH1Classes;
    printf "#matching pairs = %o\n", #R`MatchingPairs;
end procedure;

