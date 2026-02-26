intrinsic IntegralSimplifiedModel(X::CrvHyp) -> CrvHyp
{ Given a hyperelliptic curve X/Q returns an integral model y^2=f(x).  Will perform easy reductions (but avoids any hard factorizations). }
    require BaseRing(X) eq Rationals(): "Input hyperelliptic curve must be defined over Q.";
    f := HyperellipticPolynomials(SimplifiedModel(X));
    R := Parent(f); c := Coefficients(f);
    P,b := PrimeDivisors([Numerator(a):a in c] cat [Denominator(a):a in c]:AllowComposites);
    r := &*[Rationals()|p^Min([Floor(Valuation(a,p,b)/2):a in c|a ne 0]):p in P];
    c := [r^-2*a:a in c]; assert &and[Denominator(a) eq 1:a in c];
    r := &*[Rationals()|p^Min([Floor(Valuation(c[i],p,b)/(i-1)):i in [2..#c]|c[i] ne 0]):p in P];
    c := [r^(1-i)*c[i]:i in [1..#c]]; assert &and[Denominator(a) eq 1:a in c];
    return HyperellipticCurve(R!c);
end intrinsic;

intrinsic NormalizeEvenModel(F::RngMPolElt) -> RngMPolElt
{ Given a smooth plane quartic F(X,Y,Z)=0 in which only even powers of Y appear, returns a monic integral model Y^4 + g(X,Z)*Y^2 + h(X,Z). }
    R := Parent(F);
    require Degree(F) eq 4 and Rank(R) eq 3 and IsHomogeneous(F) and BaseRing(R) eq Rationals(): "Input polynomial must be a homogenous smooth plane quartic over Q.";
    require Evaluate(F,[R.1,-R.2,R.3]) eq F: "Only even powers of Y should appear in F(X,Y,Z)";
    c,m := CoefficientsAndMonomials(F);
    d := c[Index(m,R.2^4)];
    F := F/d;
    d := LCM([Denominator(c):c in Coefficients(F)]);
    F := Evaluate(F,[d*R.1,R.2,d*R.3]);
    c,m := CoefficientsAndMonomials(F); assert &and[Denominator(c[i]) eq 1: i in [1..#c]];
    P,b := PrimeDivisors([Numerator(c[i]):i in [1..#c]|Degree(m[i],1) gt 0]:AllowComposites);
    d := &*[Integers()|p^Min([Floor(Valuation(c[i],p,b)/Degree(m[i],1)):i in [1..#c]|Degree(m[i],1) gt 0]):p in P];
    F := Evaluate(F,[R.1/d,R.2,R.3]);
    c,m := CoefficientsAndMonomials(F); assert &and[Denominator(c[i]) eq 1: i in [1..#c]];
    P,b := PrimeDivisors([Numerator(c[i]):i in [1..#c]|Degree(m[i],3) gt 0]:AllowComposites);
    d := &*[Integers()|p^Min([Floor(Valuation(c[i],p,b)/Degree(m[i],3)):i in [1..#c]|Degree(m[i],3) gt 0]):p in P];
    F := Evaluate(F,[R.1,R.2,R.3/d]);
    c := Coefficients(F); assert &and[Denominator(c[i]) eq 1: i in [1..#c]];
    return F;
end intrinsic;

intrinsic NormalizeEvenModel(C::CrvPln) -> CrvPln
{ Given a smooth plane quartic C: F(X,Y,Z)=0 in which only even powers of Y appear, returns a monic integral model Y^4 + g(X,Z)*Y^2 + h(X,Z). }
    require IsEven(C,2): "Only even powers of Y may appear in C: f(X,Y,Z)=0.";
    return PlaneCurve(NormalizeEvenModel(DefiningPolynomial(C)));
end intrinsic;

intrinsic g3Hyperelliptic (C::Crv) -> BoolElt, CrvHyp
{ Determines whether the genus 3 curve C/Q is geometrically hyperelliptic, and if so returns an isomorphic hyperelliptic curve defined over Q, if possible, or over a quadratic field. }
    require Genus(C) eq 3 and BaseRing(C) eq Rationals(): "Input must be a genus 3 curve defined over Q";
    g := 3;
    if Type(C) eq CrvHyp then return true, C; end if;
    b, X := IsHyperellipticCurve(C);
    if b then return b,X; end if;
    phi := CanonicalMap(C);
    c, bHyp := CanonicalImage(C,phi);
    if not bHyp then return false,_,_; end if;
    con := Conic(Ambient(c),DefiningEquation(c));
    c_map := map<C->con| DefiningEquations(phi) : Check := false>;
    _,s := EasyFactorization(Integers()!Discriminant(con));
    if s ne 0 then
        con, m_map := MinimalModel(con);
        c_map *:= Inverse(m_map);
        c_map := Expand(c_map);
    end if;
    b,pt := HasRationalPoint(con);
    if b then
        K := Rationals();
    else
        f := DefiningEquation(con);
        f *:= LCM([Denominator(c):c in Coefficients(f)]);
        R<x> := PolynomialRing(Rationals());
        X := AssociativeArray();
        for t in SymmetricGroup(3) do X[t] := Evaluate(f,[x,0,1][[1,2,3]^t]); end for;
        t := Sort([t:t in Keys(X)],func<g,h|Abs(Discriminant(X[g]))-Abs(Discriminant(X[h]))>)[1];
        K<a> := NumberField(X[t]);
        // important: base change the map and extract domain/codomain (don't try to base change them independently!)
        c_map := ChangeRing(c_map,K);
        C := Domain(c_map); con := Codomain(c_map);
        pt := con!([a,0,1][[1,2,3]^t]);
    end if;
    if IsAffine(C) then
        c_map := mp * c_map where mp is Restriction(Inverse(ProjectiveClosureMap(Ambient(C))), ProjectiveClosure(C),C);
    end if;
    P1 := Curve(ProjectiveSpace(K,1),[]);
    p1_map := Expand(c_map * Inverse(Parametrization(con,pt,P1)));
    delete con,c_map;
    f_x := FunctionField(C)!(p1/p2) where p1,p2 := Explode(DefiningPolynomials(p1_map));
    P := PolynomialRing(K); X:=P.1;
    AFF,mpFF := AlgorithmicFunctionField(FunctionField(C));
    d := 2*g+2;
    x := mpFF(f_x);
    vec := [AFF!1,x]; 
    for i in [2..d] do Append(~vec,x*vec[i]); end for;
    v := BasisOfHolomorphicDifferentials(AFF)[1]/Differential(x);
    vec := [w*e : e in Reverse(vec)] cat [vec[i] : i in [1..2*g]] where w is v^2;
    rels := Basis(Relations(vec,K));
    delete vec;
    rels := EchelonForm(Matrix(rels));
    rel := Eltseq(rels[Nrows(rels)]);
    r := 1;
    while rel[r] eq K!0 do r +:= 1; end while;
    assert r le g+1;
    R := &+[rel[i]*X^(d+1-i) : i in [r..d+1]];
    S := - &+[rel[i+d+2]*X^i : i in [0..d-3]];
    U,V := SquareFree(S);
    pol_x := U*R; Py := U*V;
    f_y := Inverse(mpFF)(Evaluate(Py,x)/v);
    assert (d1 eq d) or (d1 eq d-1) where d1 is Degree(pol_x);
    assert Degree(GCD(pol_x,Derivative(pol_x))) eq 0;
    X := HyperellipticCurve(pol_x);
    mp_eqns := [f_x,f_y,1];
    return true,X;
end intrinsic;

intrinsic Genus3DoubleCover(E::CrvEll, DnumQ::DivCrvElt, Q::PtEll: SizeBound:=0) -> RngIntElt, Crv
{ Given an element f of the function field K of genus 1 curve E/Q with poles at 4 places, each of odd order, returns a genus 3 curve X/Q corresponding to the function field K(sqrt(f)) (or a twist thereof).
  The returned genus 3 curve is either a smooth plane quartic or hyperelliptic curve given by an integral model; if no hyperelliptic model y^2=g(x) of X/Q exists, a twist of X that admits such a model will be returned instead.
  The returned double cover X -> E determines an abelian surface A for which Jac(X) ~ A x E (this E will be a quadratic twist of the original E if X was twisted).
  The parameter TrialDivisionBound can be used to control attempts to factor potentially large discriminants (needed for hyperelliptic X that do not admit a hyperelliptic model over Q).
  The first return value will be 0 if the cover could not be constructed (e.g. due to the TrialDivisionBound), 1 if X is a smooth plane quartic, 2 if X is hyperelliptic, 3 if X is geometrically hyperelliptic and a twist was returned.
  The optional parameter SizeBound can be used to force an early abort on hyperelliptic cases where the equations or invariants involve more than SizeBound characters/digits.
}
    // We first try to construct the double cover directly via the ramification divisor (this won't always work, e.g. in the hyperelliptic case)
    D0 := Divisor(Q) + Divisor(Zero(E));
    e := Basis(D0)[1];
    D := DnumQ - 2*Divisor(Q) - 2*Divisor(Zero(E));
    b,f := IsPrincipal(D); assert b;
    P2 := ProjectiveSpace(Rationals(), [1,1,1]);
    phi := ProjectiveMap([e,f,1], P2);
    R<x,y> := PolynomialRing(Rationals(),2);
    X := PlaneCurve(Homogenize(Evaluate(DefiningEquation(Image(phi)),[x,y^2,1])));
    if not IsSingular(X) and Genus(X) eq 3 and IsEven(X,2) then return 1,NormalizeEvenModel(X); end if;

    // The direct approach did not work, which indicates that the curve is geometrically hyperelliptic
    // Now we instead the function field generated by sqrt(f) to construct a model
    FF<x,y> := FunctionField(E);
    FF2<y>, rho_alg := AlgorithmicFunctionField(Parent(f));
    _<x> := BaseField(FF2);
    f2 := rho_alg(f);
    R<Z> := PolynomialRing(FF2);
    KF<a> := ext<FF2 | Z^2 - f2>;
    // Find an equation for the canonical image, or a hyperelliptic equation.
    LF := AbsoluteFunctionField(KF);
    g := DefiningPolynomial(LF);
    // if g is horrible, quit now
    if SizeBound gt 0 and #sprint(g) gt SizeBound then return -1,_; end if;
    X0 := Curve(AffineSpace(Parent(g)), g);
    hyp, X := g3Hyperelliptic(X0);
    if not hyp then return -2,_; end if; // this should never happen
    if BaseRing(X) eq Rationals() then return 2,X; end if;
    // We have a hyperelliptic model over a quadratic field with rational Shioda invariants we can use to create a twist over Q
    // Normalizing the Shioda invariants not only puts them over Q, it will try to minimize their size be removing common (weighted) factors
    // This may require factoring some large integers if the curve equation is horrible
    // We set the Easy flag to use the EasyFactorization intrinsic (in utils.m) which will not attempt hard factorizations
    if SizeBound gt 0 and #sprint(X) gt SizeBound then return -1,_; end if;
    I := NormalizedShiodaInvariants(X:Easy);
    if SizeBound gt 0 and #sprint(I) gt SizeBound then return -1,_; end if;
    try // this can fail with "runtime error infinite loop" if the Shioda invariants are too large and SizeBound will not always avoid this
        X := HyperellipticCurveFromShiodaInvariants(I:minimize:=false);
    catch e
        return -3,_; // this should never happen in theory, but the reconstruction code may give up if it seems hopeless
    end try;
    if not BaseRing(X) eq Rationals() then return -4,_; end if; // this should never happen

    // We want to minimize our model for X before twisting, but we need to be careful to avoid hard factorizations
    // We use EasyFactorization to test the factorizability of the discriminant before calling ReducedMinimalWeierstrassModel
    D := Abs(Integers()!Discriminant(X));
    _,s := EasyFactorization(D);
    if s eq 0 then return -5,_; end if; // this will happen if X has bad reduction at two large primes
    X := ReducedMinimalWeierstrassModel(X);
    D := Integers()!(Discriminant(X)*Discriminant(E)); // need to include disc(E) because E might not be twist-minimal
    Q := [ p mod 4 eq 3 select -p else p : p in PrimeDivisors(D)|IsOdd(p)];
    if IsEven(D) then Q := [-4,-8] cat Q; end if;
    A := []; B := [];
    p := 2; cnt := 0; lastr := 0;
    while true do
        p := NextPrime(p);
        if D mod p eq 0 or TraceOfFrobenius(E,p) eq 0 then continue; end if;
        LE := LPolynomial(ChangeRing(E,GF(p)));
        LX := LPolynomial(ChangeRing(X,GF(p)));
        if IsDivisibleBy(LX,LE) then
            if IsDivisibleBy(LX,Evaluate(LE,-Parent(LE).1)) then continue; end if;
            Append(~B,GF(2)!0);
        elif IsDivisibleBy(LX,Evaluate(LE,-Parent(LE).1)) then
            Append(~B,GF(2)!1);
        else
            // This can happen when X and/or E has extra automorphisms, the twist obtained from the Shioda invariants
            // might not cover any of the (standard) quadratic twists of E.  We won't try to handle this (rare) case.
            return -6,_;
        end if;
        Append(~A,[GF(2)|LegendreSymbol(q,p) eq 1 select 0 else 1:q in Q]);
        if #A lt #Q then continue; end if;
        r := Rank(Matrix(A));
        // If two distinct twists of E are isogeny factors of Jax(X) we will never get a full rank matrix
        // So we hueristically assume that if the rank has not changed in the last 10 primes we can use any twist that works
        if r lt #Q then
            if #A eq #Q then lastr := r; continue; end if;
            if r eq lastr then cnt +:= 1; else cnt := 0; lastr := r; end if;
            if cnt lt 10 then continue; end if;
        end if;
        b,V := IsConsistent(Transpose(Matrix(A)),Vector(B));
        if not b then return -6,_; end if; // this should never happen
        d := &*[Integers()|Q[i]:i in [1..#Q]|V[i] eq 1];
        break;
    end while;
    X := QuadraticTwist(X,d);
    // for p in PrimesInInterval(3,200) do if D mod p ne 0 then assert IsDivisibleBy(LPolynomial(ChangeRing(X,GF(p))),LPolynomial(ChangeRing(E,GF(p)))); end if; end for;
    return 3,X;
end intrinsic;


intrinsic IsEven(f::RngUPolElt) -> BoolElt
{ True if f(x) = f(-x), false otherwise. }
    return f eq Evaluate(f,-Parent(f).1);
end intrinsic;

intrinsic IsEven(C::CrvHyp) -> BoolElt
{ True if C is of the form y^2+h(x^2)*y = f(x^2), false otherwise. }
    f,h := HyperellipticPolynomials(C);
    return IsEven(f) and IsEven(h);
end intrinsic;

intrinsic IsEven(f::RngMPolElt, k::RngIntElt) -> BoolElt
{ True if f(x_1,...,x_k,...x_n) = f(x_1,...,-x_k,...,x_n), false otherwise. }
    R := Parent(f);
    v := [R.i:i in [1..Rank(R)]];
    require k gt 0 and k le #v: "Second paramter should be an integer between 1 and the number of variables in f";
    v[k] := -v[k];
    return f eq Evaluate(f,v);
end intrinsic;

intrinsic IsEven(f::RngMPolElt) -> BoolElt, RngIntElt
{ True if f(x_1,...,x_k,...x_n) = f(x_1,...,-x_k,...,x_n) for some k, false otherwise; returns k as the second value if true. }
    for k in [1..Rank(Parent(f))] do if IsEven(f,k) then return true,k; end if; end for;
    return false,_;
end intrinsic;

intrinsic IsEven(C::CrvPln, k::RngIntElt) -> BoolElt, RngIntElt
{ True if the defining polynomial for C is even in one of its variables, false otherwise; second return value is the index 1,2,3 of the variable. }
    f := DefiningPolynomial(C);
    return IsEven(f,k);
end intrinsic;

intrinsic IsEven(C::CrvPln) -> BoolElt, RngIntElt
{ True if the defining polynomial for C is even in one of its variables, false otherwise; second return value is the index 1,2,3 of the variable. }
    f := DefiningPolynomial(C);
    b,k := IsEven(f);
    if b then return b,k; else return b; end if;
end intrinsic;

function transform(f,a,b,c,d)
    R<X,Z> := PolynomialRing(BaseRing(f),2);
    // homogenize to even degree polynomial
    cf := Coefficients(f); n := 2*Ceiling(Degree(f)/2);
    F := &+[cf[i+1]*X^i*Z^(n-i):i in [0..#cf-1]];
    return Evaluate(Evaluate(F,[a*X+b*Z,c*X+d*Z]),[Parent(f).1,1]);
end function;

intrinsic EvenModels(f::RngUPolElt) -> SeqEnum[RngUPolElt]
{ Given a squarefree polynomial f(x) of deg >= 5 attempts to find even polynomials g(x) whose homogenization is GL2-equivalent to that of f
(meaning that G(X,Z) = F(a*X+b*Z,c*X+d*Z) for some invertible matrix [[a,b],[c,d]], where G and F are the homogenizations of g and f). }
    K := BaseRing(f);
    x := Parent(f).1;
    // Get automorphism group of y^2=f(x), this will fail if f(x) is not squarefree and of degree at least 5, or if char(K)=2
    G, phi := AutomorphismGroupOfHyperellipticCurve(f : explicit := true); // 
    A := [phi(g)[1]:g in G|Order(g) eq 2 and not IsScalar(phi(g)[1])]; // we are looking for non-hyperelliptic involutions
    if #A eq 0 then return [Parent(f)|]; end if;
    // reduce A modulo hyperelliptic involution (use ReducedAutomorphismGroupOfHyperellipticCurve above once infinite memory bug is fixed!)
    AA := [A[1]]; for a in A[2..#A] do ainv := a^-1; if &and[not IsScalar(ainv*b):b in AA] then Append(~AA,a); end if; end for; A := AA;
    // M = [[a,b],[c,d]], when c = 0 we have x -> (a/d)x + b/d and  (a/d)^2*x + (a/d)(b/d) + (b/d) = x, so a/d=-1 (otherwise scalar)
    L := [Parent(f)|transform(f,1,M[1,2]/(2*M[2,2]),0,1):M in A|M[2,1] eq 0]; // infinity and -b/(2*d) are fixed, move -b/(2*d) to zero
    for M in A do
        a,b,c,d := Explode(Eltseq(M));
        if c eq 0 then continue; end if;
        // Solve cx^2 + (d-a)x - b = 0 to find fixed points
        s,r := IsSquare(K!((d-a)^2 + 4*b*c));
        if not s then continue; end if;
        g := transform(f,((d-a)-r)/(2*c),((a-d)-r)/(2*c),-1,1);
        Append(~L,g);
    end for;
    if K eq Rationals() then L := [g*LCM([Denominator(c):c in Coefficients(g)])^2:g in L]; end if; // make integral over Q
    assert &and[IsEven(g):g in L];
    return L;
end intrinsic;

intrinsic EvenModels(C::CrvHyp) -> SeqEnum[RngUPolElt]
{ Attempts to transform the genus 3 hyperelliptic curve C to a model of the form y^2 = f(x^2), returns a boolean and the transformed model, if found. }
    L := EvenModels(HyperellipticPolynomials(SimplifiedModel(C)));
    return [HyperellipticCurve(f):f in L];
end intrinsic;

intrinsic Genus2CurveFromEvenModel(C::CrvHyp) -> CrvHyp
{ Given a genus 3 hyperelliptic curve of the form y^2 = f(x^2) returns the genus 2 hyperelliptic curve y^2 = x*f(x). }
    f,h := HyperellipticPolynomials(C);
    require IsEven(f) and Degree(f) eq 8 and h eq 0: "The input curve C must have a model of the form y^2=f(x^2) with deg(f)=4.";
    return HyperellipticCurve(Parent(f).1 * Parent(f)![c[i]:i in [1..9 by 2]]) where c:=Coefficients(f);
end intrinsic;

intrinsic Genus1CurveFromEvenModel(C::CrvHyp) -> CrvHyp
{ Given a genus 3 hyperelliptic curve of the form y^2 = f(x^2) returns the genus 1 curve y^2 = f(x). }
    f,h := HyperellipticPolynomials(C);
    require IsEven(f) and Degree(f) eq 8 and h eq 0: "The input curve C must have a model of the form y^2=f(x^2) with deg(f)=4.";
    return HyperellipticCurve(Parent(f)![c[i]:i in [1..9 by 2]]) where c:=Coefficients(f);
end intrinsic;

intrinsic EvenModels(f:RngMPolElt) -> SeqEnum[RngMPolElt]
{ Given a homogeneous quartic f(x,y,z)=0 over Q that defines a smooth plane quartic with an involution, returns a list of isomorphic models y^4 + h(x,z)*y^2 + g(x,z) = 0. }
    R := Parent(f);
    require BaseRing(R) eq Rationals() and Rank(R) eq 3 and IsHomogeneous(f) and Degree(f) eq 4: "Input polynomial f should be a ternary quartic form over Q.";
    L := [Parent(f)|];
    try
        G,phi := AutomorphismGroupOfTernaryQuartic(f:explicit); // this can fail, the algorithm doesn't handle some corner cases
    catch e
        b,k := IsEven(f);
        if not b then return L; end if;
        F := k eq 2 select f else (k eq 1 select Evaluate(f,[R.2,R.1,R.3]) else Evaluate(f,[R.1,R.3,R.2]));
        return [NormalizeEvenModel(F)];
    end try;
    M_standard := Matrix([ [1,0,0], [0,-1,0], [0,0,1] ]);
    sts := false;
    for g in G do
        if Order(g) ne 2 then continue; end if;
        M := phi(g);
        D := Determinant(M);
        r:=&*[Integers()|a[1]^ExactQuotient(a[2],3):a in A] where A:=Factorization(Numerator(D));
        s:=&*[Integers()|a[1]^ExactQuotient(a[2],3):a in A] where A:=Factorization(Denominator(D));
        M *:= -Sign(D)*s/r;
        b,N := IsSimilar(M, M_standard);
        if not b then continue; end if;
        F := Evaluate(f, [ &+[ (N^(-1))[i,j]*R.j : j in [1..3]] : i in [1..3]]);
        Append(~L,NormalizeEvenModel(F));
    end for;
    assert &and[IsEven(g,2):g in L];
    return L;
end intrinsic;

intrinsic EvenModels(C::CrvPln) -> SeqEnum[RngMPolElt]
{ Given a smooth plane quartic curve over Q with an involution, returns a list of isomorphic models y^4 + h(x,z)*y^2 + g(x,z) = 0. }
    return [PlaneCurve(f) : f in  EvenModels(DefiningPolynomial(C))];
end intrinsic;

intrinsic Genus1CurveFromEvenModel(C::CrvPln) -> CrvHyp
{ Given a smooth plane quartic curve of the form y^4 + h(x,z)*y^2 + g(x,z) = 0 returns the genus 1 curve y^2 + h(x,1)*y = -g(x,1). }
    require Degree(C) eq 4: "Input curve must be a smooth plane quartic over Q";
    f := DefiningPolynomial(C); R := Parent(f);
    c,m := CoefficientsAndMonomials(f);
    RQ<x> := PolynomialRing(BaseRing(R));
    h := RQ![i gt 0 select c[i] else 0 where i:=Index(m,R.1^n*R.2^2*R.3^(2-n)):n in [0..2]];
    g := RQ![i gt 0 select c[i] else 0 where i:=Index(m,R.1^n*R.3^(4-n)):n in [0..4]];
    require f eq R.2^4 + &+[Coefficient(h,i)*R.1^i*R.2^2*R.3^(2-i):i in [0..2]] + &+[Coefficient(g,i)*R.1^i*R.3^(4-i):i in [0..4]]:
        "Input curve must have the form y^4 + h(x,z)*y^2 + g(x,z) = 0";
    return HyperellipticCurve(-g,h);
end intrinsic;

intrinsic Genus2CurveFromEvenModel(C::CrvPln) -> BoolElt, CrvHyp
{ Given a smooth plane quartic curve of the form y^4 + h(x,z)*y^2 + g(x,z) = 0 with g(x,z) a product of two quadratics such that the 3 x 3 matrix whose rows are given by the coefficients of these two quadratics and h, returns the genus 2 curve to which the input curve admits a degree-2 map (via Ritzenthaler-Romagny). }
    require Degree(C) eq 4: "Input curve must be a smooth plane quartic";
    f := DefiningPolynomial(C); R := Parent(f);
    c,m := CoefficientsAndMonomials(f);
    RQ<x> := PolynomialRing(BaseRing(R));
    h := RQ![i gt 0 select c[i] else 0 where i:=Index(m,R.1^n*R.2^2*R.3^(2-n)):n in [0..2]];
    g := RQ![i gt 0 select c[i] else 0 where i:=Index(m,R.1^n*R.3^(4-n)):n in [0..4]];
    require f eq R.2^4 + &+[Coefficient(h,i)*R.1^i*R.2^2*R.3^(2-i):i in [0..2]] + &+[Coefficient(g,i)*R.1^i*R.3^(4-i):i in [0..4]]:
        "Input curve must have the form y^4 + h(x,z)*y^2 + g(x,z) = 0";
    A,c := Factorization(g);
    if Max([Degree(a[1]):a in A]) eq 1 then
        g1 := c*A[1][1]*(#A gt 1 select A[2][1] else A[1][1]);
    elif Max([Degree(a[1]):a in A]) eq 2 then
        g1 := c*[a[1]:a in A|Degree(a[1]) eq 2][1];
    else return false,_; end if;
    g2 := ExactQuotient(g,g1);
    M := Matrix([[Coefficient(g1,i):i in [2..0 by -1]],
                 [Coefficient(-h,i):i in [2..0 by -1]],
                 [Coefficient(g2,i):i in [2..0 by -1]]]);
    b,N := IsInvertible(M);
    if not b then return false,_; end if;
    a := RQ![N[1,1],2*N[2,1],N[3,1]];
    b := RQ![N[1,2],2*N[2,2],N[3,2]];
    c := RQ![N[1,3],2*N[2,3],N[3,3]];
    return true,HyperellipticCurve(b*(b^2-a*c));
end intrinsic;
