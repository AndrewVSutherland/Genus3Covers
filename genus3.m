/*
  Depends on utils.m
  Implements the following intrinsics relevant to genus 3 curves

  SPQIsIsomorphic
  SPQDiscriminant
  SPQInvariants
  GHIsIsomorphic
  GHDiscriminant
  GHShiodaInvariants
  GHHyperellipticModel
  Genus3Curve
*/

intrinsic HasRationalPointImproved(C::CrvCon) -> .
{ Deals with algebraic closure. }
    F := BaseField(C);
    if Type(F) eq FldAC then
        C0 := ChangeRing(C, Rationals());
        test, P := HasRationalPoint(C0);
        if test then return true, C ! [ P[1], P[2], P[3] ]; end if;
        R := PolynomialRing(F);
        p := Evaluate(DefiningPolynomial(C), [R.1,0,1]);
        rt := Roots(p)[1][1];
        return true, C ! [rt, 0, 1];
    end if;
    return HasRationalPoint(C);
end intrinsic;

// functions to convert exponent vectors to monomials and back (from Ed to Bd and back)
function monomial(e,R) return &*[R.i^e[i]:i in [1..3]]; end function;
function exponent(m) return <Degree(m,i):i in [1..3]>; end function;

// Return dense array of coefficients of given ternary form of degree at most 4 in lex monomial order
function tf_coeffs(f)
    d := Degree(f);
    a := [BaseRing(Parent(f))!0 : i in [1..Binomial(Degree(f)+2,2)]];
    m := MonomialsOfDegree(Parent(f),d);
    t := Monomials(f);  c:=Coefficients(f);
    for i:=1 to #t do a[Index(m,t[i])] := c[i]; end for;
    return a;
end function;

// Given ternary forms f0,f1,f1 of degree d, evaluate the linear operator D_{f0,f1,f2}:C[x]_{d-1}* --> C[x]_{2d-2}
// (defined in Section 2.1 as the determinant of a 3x3 matrix) on a basis monomial u in B_{d-1}
function tf_D(fs,u)
    R:=Parent(fs[1]);
    function Fi (i,u)
        r:=[R!0,0,0];
        v:=exponent(u);
        for t in Terms(fs[i]) do
            e:=exponent(t);
            // figure out which Fij is relevant to this term (only one will be)
            if e[1] gt v[1] then j:=1; else j:= e[2] gt v[2] select 2 else 3; end if;
            r[j] +:= Coefficients(t)[1] * monomial(<e[k] - (k eq j select v[j]+1 else 0):k in [1..3]>,R);
        end for;
        return r;
    end function;
    return Determinant(Matrix([Fi(i,u):i in [1..3]]));
end function;

// Evaluates the linear operator T_{f0,f1,f2}:C[x]_{d-2}^3 --> C[x]_{2d-2} defined in Section 2.1 as the product
// of a polynomial fi and a monomial w;  Here we are taking (w,0,0),(0,w,0),(0,0,w) with w ranging over monomials
// of degree d-2 as a basis for C[x]_(d-2}^3, which is why only need one of the fi
function tf_T(fi,w)
    return tf_coeffs(fi*w);
end function;

// Given three ternary forms f:=[f0,f1,f2,f3] of degree d, compute the matrix of the linear operator Phi_{f0,f1,f2}
// as defined in Section 2.1 of the paper.
// The first binom(d+1,2) rows are values of tf_D(f,v) with v identifies a monomial of degree d-1
// The last 3*binom(d,2) rows are values of tf_T(fi,w) where w identifies a monomial of degree d-2
// Our ordering of the rows is arbitrary, this introduces a sign ambiguity that we fix in tf_res
function phi_matrix(f)
    assert #f eq 3;
    d:=Degree(f[1]); assert d gt 0;
    R:=Parent(f[1]);
    Trows:=[];
    if d ge 2 then for i in [1..3] do for w in MonomialsOfDegree(R,d-2) do Append(~Trows,tf_T(f[i],w)); end for; end for; end if;
    Drows:=[tf_coeffs(tf_D(f,v)):v in MonomialsOfDegree(R,d-1)];
    return Matrix(Trows cat Drows);
end function;

// given three ternary forms f:=[f0,f1,f2] of degree d, compute their resultant R_d(f0,f1,f2)
function tf_res(f)
    assert #f eq 3;
    d := Degree(f[1]); assert d gt 0;
    s := Determinant(phi_matrix([Parent(f[1]).i^d:i in [1..3]]));
    return s*Determinant(phi_matrix(f));
end function;

// Given a ternary form f, compute its discriminant
function tf_disc(f)
    if Type(f) eq SeqEnum and #f eq 1 then f:=f[1]; end if;
    d:=Degree(f);
    assert d gt 1;
    return ExactQuotient(tf_res([Derivative(f,Parent(f).i):i in [1..3]]),-d^(d^2-3*d+3));
end function;

function min_disc(f:D:=tf_disc(f))
    if Type(f) eq SeqEnum and #f eq 1 then f:=f[1]; end if;
    D := Integers()!Abs(D);
    if Max([Valuation(D,p):p in PrimeDivisors(D)]) lt 9 then return f, D; end if;
    g := Parent(f)!MinimizeReducePlaneQuartic(f);
    if g eq f then return f, D; end if;
    E := Integers()!Abs(tf_disc(g));
    if E eq D then return f, D; end if;
    b,n,e := IsPower(ExactQuotient(D,E));
    assert b and e mod 9 eq 0;
    return g,E;
end function;

intrinsic TernaryFormDiscriminant(f::RngMPolElt) -> RngIntElt
{ Returns the discriminant of a ternary form. }
    require VariableWeights(Parent(f)) eq [1,1,1] and IsHomogeneous(f) and Degree(f) gt 1: "Input must be a ternary form of degree at least 2.";
    d := tf_disc(f);
    if Type(d) eq FldRatElt and Denominator(d) eq 1 then d := Integers()!d; end if;
    return d;
end intrinsic;

intrinsic SPQDiscriminant(f::RngMPolElt) -> RngIntElt
{ Returns the discriminant of a ternary quartic form. }
    require VariableWeights(Parent(f)) eq [1,1,1] and IsHomogeneous(f) and Degree(f) eq 4: "Input must be a ternary quartic form.";
    return TernaryFormDiscriminant(f);
end intrinsic;

intrinsic Homogenize(f::RngMPolElt) -> RngMPolElt
{ Given poly f(x0,x1,...x_(n-1)) in n (unweighted) variables returns homogeneous polynomial g(x_0,...,x_n) = x_n^deg(f)*f(x0/xn,...,x_(n-1)/x_n) in n+1 variables. }
    R := Parent(f);  F:= BaseRing(R);
    require Set(VariableWeights(R)) eq {1}: "Expected polynomial in unweighted variables.";
    n := Rank(R)+1;
    S := PolynomialRing(F,n);
    K := FieldOfFractions(S);
    return S!(K.n^(Degree(f))*Evaluate(f,[K.i/K.n:i in [1..n-1]]));
end intrinsic;

intrinsic Homogenize(fs::SeqEnum[RngMPolElt]) -> RngMPolElt
{ Given polys f(x0,x1,...x_(n-1)) in n (unweighted) variables returns homogeneous polynomial g(x_0,...,x_n) = x_n^deg(f)*f(x0/xn,...,x_(n-1)/x_n) in n+1 variables. }
    R := Universe(fs);  F:= BaseRing(R);
    require Set(VariableWeights(R)) eq {1}: "Expected polynomials in unweighted variables.";
    n := Rank(R)+1;
    S := PolynomialRing(F,n);
    K := FieldOfFractions(S);
    return [S!(K.n^(Degree(f))*Evaluate(f,[K.i/K.n:i in [1..n-1]])): f in fs];
end intrinsic;

intrinsic GHIsIsomorphic(q::RngMPolElt, f::RngMPolElt, g::RngUPolElt) -> BoolElt, Map
{ Given a conic q(x,y,z), a homogeneous polynomial f(x,y,z), and a univariate polynomial g(x), determines whether the geometrically hyperelliptic curve q(x,y,z)=0,w^2=f(x,y,z) is isomorphic to the hyperelliptic curve y^2=g(x).}
    require Parent(q) eq Parent(f): "Multivariate inputs should be elements of the same polynomial ring.";
    R := Parent(g);  S := Parent(q);
    require Type(S) eq RngMPol and Type(R) eq RngUPol: "First two inputs should be multivariate poynomials, third input should be a univariate polynomial.";
    // Make sure we are working over a field
    if not IsField(BaseRing(R)) then R:=ChangeRing(R,FieldOfFractions(BaseRing(R))); g := R!g; end if;
    if not IsField(BaseRing(S)) then S:=ChangeRing(S,FieldOfFractions(BaseRing(S))); q := S!q; f := S!f; end if;
    F := BaseRing(R); require BaseRing(S) eq F: "Input polynomials must be defined over a common base";
    if VariableWeights(S) eq [1,1] then q,f := Explode(Homogenize([q,f])); end if;
    require VariableWeights(S) eq [1,1,1]: "Inputs must lie in an unweighted polynomial ring of rank 2 or 3.";
    require IsHomogeneous(q) and Degree(q) eq 2: "First input should be a conic.";
    require IsHomogeneous(f) and IsEven(Degree(f)) and Degree(f) ge 4: "Second input should be bivariate or homogeneous trivariate polynomial whose homogenization is of even degree at least 4.";

    S3 := S; K3 := FieldOfFractions(S3); PP2 := ProjectiveSpace(S3);
    S2 := PolynomialRing(F, 2); K2 := FieldOfFractions(S2); PP1 := ProjectiveSpace(S2);
    h21 := hom< S2 -> R | [ R.1, 1 ] >;

    Q := Conic(PP2, q); test, P := HasRationalPointImproved(Q);
    if not test then return false, []; end if;

    phi := Parametrization(Q, P);
    DE := DefiningEquations(phi);
    h := hom< Parent(DE[1]) -> S2 | [ S2.1, S2.2 ] >;
    DE := [ h(c) : c in DE ];
    g0 := Evaluate(f, DE); g0 := h21(g0);

    test, Ls := IsGL2Equivalent(g, g0, 2*Degree(f));

    isos := [ ];
    for L in Ls do
        M := Matrix(2,2, L); M := M^(-1);
        subst := [ M[1,1]*S2.1 + M[1,2]*S2.2, M[2,1]*S2.1 + M[2,2]*S2.2 ];
        T := [ Evaluate(c, subst) : c in DE ];
        lambda := F ! (h21(Evaluate(f, T)) / g);

        R := PolynomialRing(F);
        p := R.1^2 - lambda; rts := [ tup[1] : tup in Roots(p) ];
        if #rts eq 2 then
            Append(~isos, [* T, rts[1] *]); Append(~isos, [* T, rts[2] *]);
        end if;
    end for;
    return #isos ne 0, isos;
end intrinsic;

intrinsic GHIsIsomorphic(q1::RngMPolElt, f1::RngMPolElt, q2::RngMPolElt, f2::RngMPolElt) -> BoolElt, SeqEnum
{ Given curves C1=[q1(x,y,z)=0,w^2=f1(x,y,z)] and C2=[q2(x,y,z)=0,w^2=f2(x,y,z)] with conics q1,q2 and homogeneous polys f1,f2, determines whether they are isomorphic or not. }
    S := Parent(q1);  F := BaseRing(S);
    require Rank(S) in [2,3] and Parent(q2) eq S and Parent(f1) eq S and Parent(f2) eq S: "Polynomials q1,f1,q2,f2 must be elements of the same polynomial ring, of rank 2 or 3.";
    // We want to always work over a field, even if we are given integral polys
    if not IsField(F) then F:=FieldOfFractions(F); S:=PolynomialRing(F,3); q1:=S!q1; f1:=S!f1; q2:=S!q2; f2:=S!f2; end if;
    // If inputs are not homogenous, homogenize them
    if VariableWeights(S) eq [1,1] then q1,f1,q2,f2 := Explode(Homogenize([q1,f1,q2,f2])); end if;
    require VariableWeights(S) eq [1,1,1]: "Inputs must lie in an unweighted polynomial ring of rank 2 or 3";
    require IsHomogeneous({q1,q2,f1,f2}) and Degree(q1) eq 2 and Degree(q2) eq 2 and IsEven(Degree(f1)) and IsEven(Degree(f2)) and Degree(f1) eq Degree(f2) and Degree(f1) ge 4: "Input polynomials q1,q2 should be conics, f1,f2 homogenous polynomials of the same even degree >= 4.";

    S3 := S; KS3 := FieldOfFractions(S3); PP2 := ProjectiveSpace(S3);
    S2 := PolynomialRing(F, 2); KS2 := FieldOfFractions(S2); PP1 := ProjectiveSpace(S2);
    R := PolynomialRing(F); h21 := hom< S2 -> R | [ R.1, 1 ] >;

    Q1 := Conic(PP2, q1); Q2 := Conic(PP2, q2);
    if Type(BaseRing(Q1)) eq FldRat or Type(BaseRing(Q1)) eq FldNum then
        B1 := QuaternionAlgebra(Q1);  B2 := QuaternionAlgebra(Q2);
        if not IsIsomorphic(B1, B2) then return false, []; end if;
    end if;

    test1, P1 := HasRationalPointImproved(Q1);
    test2, P2 := HasRationalPointImproved(Q2);
    if test1 ne test2 then return false, []; end if;

    if not test1 then
        p := Evaluate(q1, [ R.1, 0, 1 ]);
        K := NumberField(p);

        S := PolynomialRing(K, 3);
        hq1 := hom< Parent(q1) -> S | [ S3.1, S3.2, S3.3 ] >; q1 := hq1(q1);
        hf1 := hom< Parent(f1) -> S | [ S3.1, S3.2, S3.3 ] >; f1 := hf1(f1);
        hq2 := hom< Parent(q2) -> S | [ S3.1, S3.2, S3.3 ] >; q2 := hq2(q2);
        hf2 := hom< Parent(f2) -> S | [ S3.1, S3.2, S3.3 ] >; f2 := hf2(f2);
        L1 := [ q1, f1 ]; L2 := [ q2, f2 ];

        S3 := S; KS3 := FieldOfFractions(S3); PP2 := ProjectiveSpace(S3);
        S2 := PolynomialRing(K, 2); KS2 := FieldOfFractions(S2); PP1 := ProjectiveSpace(S2);
        R := PolynomialRing(K); h21 := hom< S2 -> R | [ R.1, 1 ] >;

        Q1 := Conic(PP2, q1);
        Q2 := Conic(PP2, q2);
        test1, P1 := HasRationalPointImproved(Q1);
        test2, P2 := HasRationalPointImproved(Q2);
        if not test2 then return false, []; end if;
    end if;
    phi1 := Parametrization(Q1, P1);
    phi2 := Parametrization(Q2, P2);

    DE1 := DefiningEquations(phi1);
    DE2 := DefiningEquations(phi2);
    h1 := hom< Parent(DE1[1]) -> S2 | [ S2.1, S2.2 ] >;
    h2 := hom< Parent(DE2[1]) -> S2 | [ S2.1, S2.2 ] >;
    DE1 := [ h1(c) : c in DE1 ];
    DE2 := [ h2(c) : c in DE2 ];

    g := h21(Evaluate(f2, DE2));
    test3, isos := GHIsIsomorphic (q1,f1,g);
    Ts := [ T : T in Set([ iso[1] : iso in isos ]) ];

    isos := [ ];
    for T in Ts do
        P1s := [ [ Evaluate(c, [i,1]) : c in T ] : i in [1..4] ];
        P2s := [ [ Evaluate(c, [i,1]) : c in DE2 ] : i in [1..4] ];
        RF<a11,a12,a13,a21,a22,a23,a31,a32,a33,lambda1,lambda2,lambda3,lambda4> := PolynomialRing(BaseRing(S3), 13);
        M := Matrix(RF, 3,3, [ a11, a12, a13, a21, a22, a23, a31, a32, a33 ]);
        lambdas := [ lambda1, lambda2, lambda3, lambda4 ];

        A := [ ];
        for i in [1..4] do
            P1 := P1s[i]; P2 := P2s[i];
            lambda := lambdas[i];
            P1 := Matrix(RF, 3,1, P1);
            P2 := Matrix(RF, 3,1, P2);
            dif := M*P1 - lambda*P2;
            for c in Eltseq(dif) do
                Append(~A, [ MonomialCoefficient(c, RF.j) : j in [1..13] ]);
            end for;
        end for;
        A := Matrix(A);
        Ker := Kernel(Transpose(A));
        assert Dimension(Ker) eq 1;
        v := Eltseq(Basis(Ker)[1]);
        U := Matrix(BaseRing(S3), 3,3, v[1..9]);
        S3rel := PolynomialRing(S2);
        h := hom< S3 -> S3rel | [ S3rel.1, S2.1, S2.2 ] >;
        rem1 := h(f1) mod h(q1);
        rem2 := h(f2^U) mod h(q1);
        lambda := BaseRing(S3) ! (rem2 / rem1);
        test4, rt := IsSquare(lambda);
        if test4 and (rt in F) then
            Useq := Eltseq(U); i := 0;
            repeat i +:= 1; Uden := Useq[i]; until Uden ne 0;
            U /:= Uden;
            if &and[ IsCoercible(F,c) : c in Eltseq(U) ] then
                Append(~isos, [* ChangeRing(U, F), F !  rt *] );
                Append(~isos, [* ChangeRing(U, F), F ! -rt *]);
            end if;
        end if;
    end for;
    return #isos ne 0, isos;
end intrinsic;

intrinsic GHPolys(A::.) -> RngMPolElt, RngMPolElt
{ Given list of lists of field elements (or corresponding string) return conic q(x,y,z) and quartic f(x,y,z).  Input may be lists of 6 and 15 coeffs, or list [[a,b],[g0,g1,g2,g3],[h0,h1,h2,h3,h4] specifying x^2-a*y^2-b*z^2 and x*(g0*y^3+g1*y^2*z+g2*y*z^2+g3*z^3) + h0*y^4+h1*y^3*z+h2*y^2*z^2+h3*y*z^3+h4*z^4. }
    R<x,y,z>:=PolynomialRing(Rationals(),3);
    if Type(A) eq MonStgElt then A := eval(A); end if;
    require Type(A) eq SeqEnum: "Input should be a list";
    if Type(A[1]) eq RngMPolElt then
        R := Universe(A);
        require #A eq 2: "Expected a pair of polynomials.";
        if VariableWeights(R) eq [1,1] then A := Homogenize(A); end if;
        require VariableWeights(R) eq [1,1,1]: "Expected a pair of (unweighted) bivariate or trivariate polynomials.";
        return A[1],A[2];
    end if;
    require #A in [2,3] and &and[Type(a) eq SeqEnum:a in A]: "Input should be list of either 2 or 3 lists of coefficients.";
    R<x,y,z>:=PolynomialRing(Universe(A[1]),3);
    require #A[1] in [2,6]: "First list should specify a conic either as a pair [a,b] for x^2-a*y^2-b*y^2 or dense coefficient list of length 6.";
    if #A[1] eq 2 then q:=x^2-A[1][1]*y^2-A[1][2]*z^2; else q:=&+[A[1][i]*M[i]:i in [1..6]] where M:=MonomialsOfDegree(R,2); end if;
    if #A eq 2 then
        require #A[2] eq 15: "Second list should be a dense coefficient list of length 15 specifying a quartic.";
        f := &+[A[2][i]*M[i]:i in [1..15]] where M:=MonomialsOfDegree(R,4);
    else
        require #A[2] eq 4 and #A[3] eq 5: "Second and third lists should have lengths 4 and 5 (specifying cubic g(y,z) and quartic h(y,z), with z^0 coefficient first).";
        f := x*&+[z^i*y^(3-i)*A[2][i+1]:i in [0..3]] + &+[z^i*y^(4-i)*A[3][i+1]:i in [0..4]];
    end if;
    return q,f;
end intrinsic;

intrinsic GHIsIsomorphic(A::SeqEnum,g::RngUPolElt) -> BoolElt
{ Given a list of polynomials (which may be a coefficient list) defining a conic cover C: q(x,y,z)=0, w^2=f(x,y,z), as well as a polynomial g, determine whether the corresponding curves are isomorphic. Conics should be specified either as (a,b) defining x^2-a*y^2-b*z^2 or homogeneous poly degree 2. }
    q1, f1 := GHPolys(A);
    return GHIsIsomorphic(q1,f1,g);
end intrinsic;

intrinsic GHIsIsomorphic(A::SeqEnum,B::SeqEnum) -> BoolElt
{ Given lists of polynomials (which may be coefficient lists) defining conic covers C: q(x,y,z)=0, w^2=f(x,y,z), determine whether they are isomorphic. Conics should be specified either as (a,b) defining x^2-a*y^2-b*z^2 or homogeneous poly degree 2. }
    q1, f1 := GHPolys(A); q2, f2 := GHPolys(B); q2 := Parent(q1)!q2; f2 := Parent(q1)!f2;
    return GHIsIsomorphic(q1,f1,q2,f2);
end intrinsic;

intrinsic GHIsIsomorphic(A::MonStgElt,B::MonStgElt) -> BoolElt
{ Given lists of polynomials (which may be coefficient lists) defining conic covers C: q(x,y,z)=0, w^2=f(x,y,z), determine whether they are isomorphic. Conics should be specified either as (a,b) defining x^2-a*y^2-b*z^2 or homogeneous poly degree 2. }
    R<x,y,z> := PolynomialRing(Rationals(),3);
    A := eval(A);  B := eval(B);
    return GHIsIsomorphic(A,B);
end intrinsic;

intrinsic GHDiscriminant (q::SeqEnum,g::SeqEnum,h::SeqEnum) -> RngIntElt
{ Computes the discriminant of the curve [x^2-q[1]*y^2-q[2]*z^2, w^2=x*(g[0]*y^3+g[1]*y^2*z+...+g[3]*z^3) + h[0]*y^4+h[1]*y^3*z+...+h[4]*z^4. }
    require #q eq 2 and #g eq 4 and #h eq 5: "Expected lists of integers of length 2,4,5";
    R<z>:=PolynomialRing(Rationals());
    a:=R!g;  b:=R!h;
    f:=(-q[1]-q[2]*z^2)*a^2+b^2;
    assert Degree(f) le 8;
    if Degree(f) le 6 then return 0; end if;
    D := Degree(f) eq 8 select Discriminant(f) else LeadingCoefficient(f)^2*Discriminant(f);
    return ExactQuotient(Integers()!(16*q[1]^2*q[2]^2*D),2^8); // Can't we remove a larger power of 2 here, e.g. 2^16?
end intrinsic;

intrinsic GHSimpleIntegralModel (q::RngMPolElt,f::RngMPolElt) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt], SeqEnum[RngIntElt]
{ Given conic q and quartic f defining curve [q(x,y,z)=0, w^2=f(x,y,z)] over Q, return lists of inteers [a,b], [g0,g1,g2,g3], [h0,h1,h2,h3.h4] defining isomorphic curve x^2-a*y^2-b*z^2=0, w^2=x*(g0y^3+g1*y^2*z+g2*y*z^2+g3*z^3)+h0*y^4+...+h4*z^4. }
    R := Parent(q);  F := BaseRing(R);
    require Parent(f) eq R: "Inputs should be elements of the same polynomial ring";
    if VariableWeights(R) eq [1,1] then q,f := Explode(Homogenize([q,f])); end if;
    require VariableWeights(R) eq [1,1,1]: "Expected a pair of (unweighted) bivariate or trivariate polynomials.";
    require IsHomogeneous(q) and Degree(q) eq 2: "First input should be a conic.";
    require IsHomogeneous(f) and Degree(f) ge 4: "Second input be a ternary quartic form.";
    qc,pi := LegendreModel(Conic(Curve(ProjectiveSpace(R),q)));
    q := pi(q);  f := pi(f);
    assert Monomials(q) eq [R.1^2,R.2^2,R.3^2];
    if Coefficients(q)[1] ne 1 then
        if not IsField(F) then F := FieldOfFractions(F); end if;
        qq := ChangeRing(q,F)/Coefficients(q)[1];
        d2 := Denominator(Coefficients(q)[2]);  d3 := Denominator(Coefficients(q)[3]);
        q := Evaluate(q,[R.1,d2*R.2,d3*R.3]);  f := Evaluate(f,[R.1,d2*R.2,d3*R.3]);
    end if;
    while true do
        T := Terms(f); C := Coefficients(f); E := [Exponents(t):t in T];
        I := [i:i in [1..#E]|E[i][1] ge 2];
        if #I eq 0 then break; end if;
        c := C[I[1]];  e := E[I[1]];
        f := f - q*c*R.1^(e[1]-2)*R.2^e[2]*R.3^e[3];
    end while;
    c := [-Coefficients(q)[2],-Coefficients(q)[3]];
    g := [MonomialCoefficient(f,R.1*R.2^(3-i)*R.3^i):i in [0..3]];
    h := [MonomialCoefficient(f,R.2^(4-i)*R.3^i):i in [0..4]];
    assert q eq R.1^2-c[1]*R.2^2-c[2]*R.3^2;
    assert f eq R.1*&+[g[i+1]*R.2^(3-i)*R.3^i:i in [0..3]] + &+[h[i+1]*R.2^(4-i)*R.3^i:i in [0..4]];
    return c,g,h;
end intrinsic;

intrinsic GHDiscriminant (q::RngMPolElt,f::RngMPolElt) -> RngIntElt
{ Computes the discriminant of the (simple integral model of the) curve [q(x,y,z)=0, w^2=f(x,y,z)]. }
    c,g,h := GHSimpleIntegralModel(q,f);
    return GHDiscriminant(c,g,h);
end intrinsic;

intrinsic GHDiscriminant (A::SeqEnum) -> RngIntElt
{ Computes the discriminant of the (simple integral model of) curve [q(x,y,z)=0, w^2=f(x,y,z)]. }
    if #A eq 3 then return GHDiscriminant(q,g,h) where q,g,h := Explode(A); end if;
    q,g,h := GHSimpleIntegralModel(q,f) where q,f := GHPolys(A);
    return GHDiscriminant(q,g,h);
end intrinsic;

intrinsic GHDiscriminant (s::MonStgElt) -> RngIntElt
{ Computes the discriminant of the (simple integral model of) curve [q(x,y,z)=0, w^2=f(x,y,z)]. }
    R<x,y,z>:=PolynomialRing(Rationals(),3);
    return GHDiscriminant(eval(s));
end intrinsic;

intrinsic GHCurve(q::RngMPolElt,f::RngMPolElt : prec:=100) -> Crv
{ Given conic q(z,y,z) and homogeneous poynomial f(x,y,z) of degree >= 3, returns curve [q(x,y,z)=0,w^2=f(z,y,x)] in [2,1,1,1] weighted projective space. }
    require Parent(q) eq Parent(f): "Polynomials must lie in the same polynomial ring.";
    if Rank(Parent(q)) eq 2 then q,f := Explode(Homogenize([q,f])); end if;
    R := Parent(q);
    require VariableWeights(R) eq [1,1,1]: "Polynomials must lie in an unweighted polynomial ring of rank 2 or 3.";
    require IsHomogeneous(q) and Degree(q) eq 2: "First input should be a conic.";
    require IsHomogeneous(f) and IsEven(Degree(f)) and Degree(f) ge 4: "Second input should be bivariate or homogeneous trivariate polynomial whose homogenization is of even degree at least 4.";
    P<w,x,y,z> := ProjectiveSpace(RationalsExtra(prec),[2,1,1,1]);
    return Curve(P,[Evaluate(q,[x,y,z]),w^2-Evaluate(f,[x,y,z])]);
end intrinsic;

intrinsic GHCurve(A::SeqEnum : prec:=100) -> Crv
{ Given conic q(z,y,z) and homogeneous poynomial f(x,y,z) of degree >= 3, returns curve [q(x,y,z)=0,w^2=f(z,y,x)] in [2,1,1,1] weighted projective space. }
    return GHCurve(q,f:prec:=prec) where q,f := GHPolys(A);
end intrinsic;

intrinsic GHCurve(A::MonStgElt : prec:=100) -> Crv
{ Given conic q(z,y,z) and homogeneous poynomial f(x,y,z) of degree >= 3, returns curve [q(x,y,z)=0,w^2=f(z,y,x)] in [2,1,1,1] weighted projective space. }
    R<x,y,z>:=PolynomialRing(Rationals(),3);
    A := eval(A);
    return GHCurve(A:prec:=prec);
end intrinsic;

intrinsic IsGHCurve(C::Crv) -> BoolElt, RngMPolElt, RngMPolElt
{ Determines whether the curve C is (exactly, not just isomorphic to a curve) of the form [q(x,y,z)=0,w^2=f(x,y,z)] in [2,1,1,1]-weighted projective space.  If so, also returns q an f. }
    if VariableWeights(CoordinateRing(Ambient(C))) ne [2,1,1,1] then return false,_,_; end if;
    p := Sort(DefiningPolynomials(C),func<a,b|Degree(a)-Degree(b)>);
    if Degree(p[1]) ne 2 or Degree(p[2]) ne 4 then return false,_,_; end if;
    q,h := Explode(p);
    R := Parent(h);  F := BaseRing(R);
    f := R.1^2 - h;
    for g in [q,f] do if Evaluate(g,[0,R.2,R.3,R.4]) ne g then return false,_,_; end if; end for;
    R<x,y,z> := PolynomialRing(F,3);
    return true,Evaluate(q,[0,x,y,z]), Evaluate(f,[0,x,y,z]);
end intrinsic;

intrinsic GHPolys(C::Crv) -> RngMPolElt, RngMPolElt
{ Given a curve [q(x,y,z)=0,w^2=f(x,y,z)] with q a conic and f a homogeneous poly of degree at least 3, returns q and f. }
    b,q,f := IsGHCurve(C);
    require b: "Curve is not of the form [q(x,y,z)=0,w^2-f(x,y,z)] in [2,1,1,1]-weighted projective space.";
    return q,f;
end intrinsic;

intrinsic GHHyperellipticModel(q::RngMPolElt,f::RngMPolElt:D:=0,p:=0,poly:=false) -> .
{ Returns a hyperelliptic curve (possibly defined over a quadratic extension) of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    require Parent(q) eq Parent(f): "Input polynomials lie in the same ring.";
    require D eq 0 or p eq 0: "Please specify just one of the optional parameters D or p.";
    require p eq 0 or (p gt 2 and IsPrime(p)): "Optional parameter p must be an odd prime (of good reduction).";
    if Rank(Parent(q)) eq 2 then q,f := Explode(Homogenize([q,f])); end if;
    R := Parent(q);
    require VariableWeights(R) eq [1,1,1]: "Polynomials must lie in an unweighted polynomial ring of rank 2 or 3.";
    if p gt 0 then
        F := GF(p); R := ChangeRing(R,F); P := ProjectiveSpace(R);
        h := hom< Parent(q) -> R | [ R.1, R.2, R.3 ] >; q := h(q); f := h(f);
    else
        P := ProjectiveSpace(R); F := BaseRing(P);
        if not HasRationalPointImproved(Conic(Curve(P,q))) then
            assert p eq 0;
            while true do
                while not IsFundamentalDiscriminant(D) do  D := D gt -3 select -3 else D-1; end while;
                if HasRationalPointImproved(Conic(ChangeRing(Curve(P,q),QuadraticField(D)))) then break; end if;
                D -:= 1;
            end while;
            F := QuadraticField(D); R := ChangeRing(R,F); P := ProjectiveSpace(R);
            h := hom< Parent(q) -> R | [ R.1, R.2, R.3 ] >; q := h(q); f := h(f);
        end if;
    end if;
    Rt<t>:=PolynomialRing(F);
    C := Conic(Curve(P,q));
    _,P := HasRationalPointImproved(C);
    phi := Parametrization(C,P);
    h := Evaluate(Evaluate(f,DefiningPolynomials(phi)),[t,1]);
    if p gt 0 and IsEven(Degree(h)) then
        r := Roots(h);
        if #r gt 0 then h := ReciprocalPolynomial(Evaluate(h,t+r[1][1])); end if;
    end if;
    if IsOdd(Degree(h)) and not IsMonic(h) then c := LeadingCoefficient(h);  h := c^(Degree(h)-1)*Evaluate(h,t/c); end if;
    return poly select h else HyperellipticCurve(h);
end intrinsic;

intrinsic GHHyperellipticModel(A::SeqEnum:D:=0,p:=0,poly:=false) -> .
{ Returns a hyperelliptic curve (possibly defined over a quadratic extension) of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    q,f := GHPolys(A);
    return GHHyperellipticModel(q,f:D:=D,p:=p,poly:=poly);
end intrinsic;

intrinsic GHHyperellipticModel(A::MonStgElt:D:=0,p:=0,poly:=false) -> .
{ Returns a hyperelliptic curve (possibly defined over a quadratic extension) of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    q,f := GHPolys(eval(A));
    return GHHyperellipticModel(q,f:D:=D,p:=p,poly:=poly);
end intrinsic;

intrinsic GHHyperellipticModel(C::Crv:D:=0,p:=0,poly:=false) -> .
{ Returns a hyperelliptic curve (possibly defined over a quadratic extension) of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    q,f := GHPolys(C);
    return GHHyperellipticModel(q,f:D:=D,p:=p,poly:=poly);
end intrinsic;


intrinsic QuadraticHyperellipticCurveString(C::CrvHyp) -> MonStgElt
{ Given a hyperelliptic curve C/Q(sqrt(D)) returns a string [a_8,b_8]*x^8+[a_7,b_7]*x^7+...+[a_0,b_0] such that C: y^2 = (a_8+b_8*Sqrt(D)x^8 + ... + a_0+b_0*Sqrt(D) (appropriate for input to hwlpolys.}
    K := BaseRing(C);
    require IsNumberField(K) and AbsoluteDegree(K) eq 2: "Hyperelliptic curve must be defined over a quadratic field.";
    f := HyperellipticPolynomials(SimplifiedModel(C));
    D := Discriminant(RingOfIntegers(K));
    R<t> := PolynomialRing(Rationals());
    K := NumberField(t^2-D);
    b,pi := IsIsomorphic(BaseRing(f),K);
    assert b;
    c := [pi(a):a in Coefficients(f)];
    R<x> := PolynomialRing(K);
    // Make sure constant coefficient is nonzero
    f := R!c;
    S := [Evaluate(f,x+K![a,b]):a in [-5..5],b in [-5..5]];
    S := [f:f in S|&and[n ne 0:n in Eltseq(Evaluate(f,0))]];
    assert #S ne 0;
    f := Sort(S,func<a,b|&+[&+[Abs(n):n in Eltseq(c)]:c in Coefficients(a)] - &+[&+[Abs(n):n in Eltseq(c)]:c in Coefficients(b)]>)[1];
    c := Coefficients(f);
    d := LCM([Denominator(a):a in c]);
    c := [d^2*a:a in c];
    r := [Sprintf("%o*x^%o",Eltseq(c[i]),i):i in [8,7,6,5,4,3,2]|i le #c and c[i] ne 0];
    if c[2] ne 0 then Append(~r,Sprintf("%o*x",Eltseq(c[2]))); end if;
    if c[1] ne 0 then Append(~r,Sprintf("%o",Eltseq(c[1]))); end if;
    return StripWhiteSpace(Join(r,"+"));
end intrinsic;

intrinsic GHShiodaInvariants(q::RngMPolElt,f::RngMPolElt) -> SeqEnum[RngIntElt]
{ The normalized Shioda invariants of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    return NormalizedShiodaInvariants(GHHyperellipticModel(q,f));
end intrinsic;

intrinsic GHShiodaInvariants(A::SeqEnum) -> SeqEnum[RngIntElt]
{ The normalized Shioda invariants of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
    q,f := GHPolys(A);
    return GHShiodaInvariants(q,f);
end intrinsic;

intrinsic GHShiodaInvariants(A::MonStgElt) -> SeqEnum[RngIntElt]
{ The normalized Shioda invariants of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
  q,f := GHPolys(eval(A));
  return GHShiodaInvariants(q,f);
end intrinsic;

intrinsic GHShiodaInvariants(C::Crv) -> SeqEnum[RngIntElt]
{ Returns a hyperelliptic curve (possibly defined over a quadratic extension) of the geometrically hyperelliptic curve [q(x,y,z)=0,w^2=f(x,y,z)]. }
  q,f := GHPolys(C);
  return GHShiodaInvariants(q,f);
end intrinsic;

intrinsic Discriminant(C::CrvPln) -> RngElt
{ Returns the discriminant of a curve of an integral plane, elliptic, or, hyperelliptic curve. }
    f:=DefiningPolynomial(C); f*:=LCM([Denominator(c):c in Coefficients(f)]); d := tf_disc(f);
    if Type(d) eq FldRatElt and Denominator(d) eq 1 then d:=Integers()!d; end if;
    return d;
end intrinsic;

intrinsic CurveDiscriminant(C::Crv) -> RngElt
{ Returns the discriminant of a curve of an integral plane, elliptic, or, hyperelliptic curve. }
    if IsSingular(C) then return 0; end if;
    require BaseRing(C) eq Rationals() or BaseRing(C) eq Integers(): "Curve must be defined over Q.";
    d := 0;
    if Type(C) eq CrvEll or Type(C) eq CrvHyp then
        d := Discriminant(C);
    elif Type(C) eq CrvPln then
        f:=DefiningPolynomial(C); f*:=LCM([Denominator(c):c in Coefficients(f)]); d := tf_disc(f);
    else
        b,q,f := IsGHCurve(C);
        if b then d := GHDiscriminant(q,f); end if;
    end if;
    if d eq 0 then error Sprintf("Don't know how to compute discriminant of curve %o.",C); end if;
    if Type(d) eq FldRatElt and Denominator(d) eq 1 then d:=Integers()!d; end if;
    return d;
end intrinsic;

intrinsic MinimalDiscriminant(C::Crv) -> RngElt
{ Returns the minimal discriminant of a curve of a plane, elliptic, or, hyperelliptic curve over Q. }
    if IsSingular(C) then return 0; end if;
    require BaseRing(C) eq Rationals() or BaseRing(C) eq Integers(): "Curve must be defined over Q.";
    d := 0;
    if Type(C) eq CrvEll then
        d := Discriminant(MinimalModel(C));
    elif Type(C) eq CrvHyp then
        d := Discriminant(ReducedMinimalWeierstrassModel(C));
    elif Type(C) eq CrvPln then
        _,d := min_disc(DefiningPolynomial(C));
    end if;
    if Type(d) eq FldRatElt and Denominator(d) eq 1 then d:=Integers()!d; end if;
    if d eq 0 then error Sprintf("Don't know how to compute minimal discriminant of curve %o.",C); end if;
    return d;
end intrinsic;


/*
All EndomorphismDescription functions return a tuple <GeomEndR, EndFieldGalId, EndRecords> where

  * GeomEndR is a lex-sorted list of pairs of integers [[m1,d1],[m2,d2],...] where [m,d] denotes M_m(D) and d=dim(D) (D is R,C,H).
  * EndFieldGalId is the small group identifier of G=Gal(K/Q),K for which End(Jac(C_K)) = End(Jac(C_Qbar))
  * EndRecords is a list of tuples, one for each subgroup H of G (up to conjugacy) ordered according to Magma subgroups ordering,
    with the format <SubgroupId,FieldPoly,EndR,EndQ,EndZ,PicNum> where

      - SubgroupId is the small group identifier of H
      - FieldPoly is a list of integer coeffs of defining poly for the fixed field F of H
      - EndR is a lex-sorted list of pairs of integers [[m,d],...] (same format as GeomEndR) describing End(Jac(C_F)) x R
      - EndQ is a lex sorted list of tuples <m,dimD,[z0,..,zn],discD,dimA> describing factorization of End(Jac(C_F)xQ) = Prod B_i
        into isotypic components B = M_m(D) with D a division algebra whose center Z is a number field
          * m is the degree of the isotypic component B as a matrix algebra over D (i.e. B is an m x m matrix algebra)
          * dimD is the Q-dimension of the division algebra D
          * [z0,...,zn] is a list of integer coeffs of a defining poly for the number field Z (center of D)
          * discD is the discriminant of D over Z (in general an O_Z-ideal, but for us a signed integer)
          * dimA is the dimension of the simple subvariety of Jac(C_F) corresponding to B
      - EndZ is a pair of integers [i,e] where i is the index of End(Jac(C_F)) in a maximal order of End(Jac(C_F)) x Q
        and e is -1,0,1 with e=-1 if D is commutative and otherwise e=1 if EndZ is an Eichler order and 0 otherwise
      - PicNum is the Picard number of Jac(C_F) (the Q-dimension of the subalgebra of EndQ fixed by the Rosati involution)
*/

intrinsic Genus3Curve(C::. : prec := 100 ) -> Crv
{ Given a list of polynomials (or their coefficients, or string representing such a list) over ZZ or QQ, returns a hyperelliptic, geometrically hyperelliptic, or nonhyperelliptic curve of genus 3 over RationalsExtra(prec) (prec:=100 by default). }
    QQ := Rationals();
    if Type(C) eq MonStgElt then
        if "y" in C or "z" in C then R<x,y,z>:=PolynomialRing(QQ,3); else
        if "Y" in C or "Z" in C then R<X,Y,Z>:=PolynomialRing(QQ,3); else
        if "x" in C then R<x>:=PolynomialRing(QQ); else
        if "X" in C then R<X>:=PolynomialRing(QQ); end if; end if; end if; end if;
        if "=" in C then C:=[eval(c):c in Split(C,"=")]; C := Homogenization(C[1]-C[2],R.3); else C := eval(C); end if;
    end if;
    QQprec := RationalsExtra(prec);
    function setprec(f) return Type(f) eq RngUPolElt select PolynomialRing(QQprec)!f else PolynomialRing(QQprec,Rank(Parent(f))) ! f; end function;
    if Type(C) eq CrvHyp then 
        require Genus(C) eq 3: "Input curve must have genus 3";
        f,h := HyperellipticPolynomials(C);
        return HyperellipticCurve(setprec(f),setprec(h));
    end if;
    if Type(C) eq CrvPln then
        require Genus(C) eq 3: "Input curve must have genus 3";
        return PlaneCurve(setprec(DefiningPolynomial(C)));
    end if;
    if Type(C) eq Crv then
        require Genus(C) eq 3: "Input curve must have genus 3";
        b,q,f := IsGHCurve(C);
        if b then return GHCurve(q,f:prec:=prec); end if;
        C := DefiningPolynomials(C);
        require #C eq 1: "Expected either a geometrically hyperelliptic curve or a plane curve";
    end if;
    if Type(C) eq RngUPolElt or Type(C) eq RngMPolElt then C := [C]; end if;
    require Type(C) eq SeqEnum: "Input should be a polynomial or a list";
    if #C eq 1 then
        if Type(C[1]) eq RngUPolElt and Degree(C[1]) in [7,8] then
            X := HyperellipticCurve(setprec(C[1]));
            require Genus(X) eq 3: "Input univariate polynomial of degree 7 or 8 does not define a (smooth) hyperelliptic curve of genus 3.";
            return X;
        end if;
        if Type(C[1]) eq RngUPolElt and Degree(C[1]) eq 4 then
            R<x,y,z> := PolynomialRing(QQprec,3);  c:=Coefficients(C[1]);
            X := PlaneCurve(y^3*z - &+[x^(i-1)*z^(5-i)*c[i]:i in [1..5]]);
            require Genus(X) eq 3: "Input univariate polynomial of degree 4 does not define a (smooth) Picard curve y^3=f(x).";
            return X;
        end if;
        if Type(C[1]) eq RngMPolElt then
            require Rank(Parent(C[1])) eq 3 and IsHomogeneous(C[1]) and Degree(C[1]) eq 4: "Single multivariate polynomial must be homogeneous of degree 4.";
            X := PlaneCurve(setprec(C[1]));
            require Genus(X) eq 3: "Input trivariate polynomial of degree 4 does not define a plane curve of genus 3.";
            return X;
        end if;
        require Type(C[1]) eq SeqEnum: "A list of length 1 should contain a polynomial or a list of coefficients";
        if #C[1] eq 5 then
            R<x,y,z> := PolynomialRing(QQprec);
            X := PlaneCurve(y^3*z - &+[x^(i-1)*z^(5-i)*C[i]:i in [1..5]]);
            require Genus(X) eq 3: "Input coefficient list of length 5 does not define a (smooth) Picard curve y^3 = f(x)";
            return X;
        end if;
        if #C[1] in [8,9] then
            X := HyperellipticCurve(PolynomialRing(QQprec)!C);
            require Genus(X) eq 3: "Input coefficient list of length 8 or 9 does not define a (smooth) hyperelliptic curve y^2=f(x) of genus 3";
            return X;
        end if;
        if #C[1] eq 15 then
            R<x,y,z> := PolynomialRing(PolynomialRing(QQprec)); M := MonomialsOfDegree(R,4);
            X := PlaneCurve(&+[C[i]*M[i]:i in [1..15]]);
            require Genus(X) eq 3: "Input coefficient list of length 15 does not define a plane curve of genus 3.";
            return X;
        end if;
        error Sprintf("Don't know how to handle a single coefficient list of length %o", #C[1]);
    end if;
    if #C eq 2 then
        if Type(C[1]) eq RngMPolElt then return GHCurve(C:prec:=prec); end if;
        if Type(C[1]) eq RngUPolElt then
            X := HyperellipticCurve(setprec(C[1]),setprec(C[2]));
            require Genus(X) eq 3: "Input pair of univariate polynomials do not define a (smooth) hyperelliptic curve of genus 3.";
            return X;
        end if;
        R<x> := PolynomialRing(QQprec);
        X := HyperellipticCurve(R!C[1],R!C[2]);
        require Genus(X) eq 3: "Input pair of lists of coefficients do not define a (smooth) hyperelliptic curve of genus 3.";
        return X;
    end if;
    if #C eq 3 then return GHCurve(C : prec:=prec); end if;
    if #C eq 5 then
        R<x,y,z> := PolynomialRing(QQprec,3);
        X := PlaneCurve(y^3*z - &+[x^(i-1)*z^(5-i)*C[i]:i in [1..5]]);
        require Genus(X) eq 3: "Input coefficient list of length 5 does not define a (smooth) Picard curve y^3 = f(x)";
        return X;
    end if;
    if #C in [8,9] then
        X := HyperellipticCurve(PolynomialRing(QQprec)!C);
        require Genus(X) eq 3: "Input coefficient list of length 8 or 9 does not define a (smooth) hyperelliptic curve y^2=f(x) of genus 3";
        return X;
    end if;
    if #C eq 15 then
        R<x,y,z> := PolynomialRing(QQprec,3); M := MonomialsOfDegree(R,4);
        X := PlaneCurve(&+[C[i]*M[i]:i in [1..15]]);
        require Genus(X) eq 3: "Input coefficient list of length 15 does not define a smooth plane quartic curve";
        return X;
    end if;
    error Sprintf("Don't know how to handle input list of length %o", #C);
end intrinsic;

intrinsic Traces(C::Crv,B::RngIntElt) -> SeqEnum
{ Returns traces of Frobenius of a genus 3 curve at all good primes up to the specified bound. }
    D := Integers()!CurveDiscriminant(C);
    P := [p : p in PrimesInInterval(1,B) | not IsDivisibleBy(D,p)];
    return [[p,p+1-#RationalPoints(ChangeRing(C,GF(p)))] : p in P];
end intrinsic;

intrinsic Traces(C::Crv,E::CrvEll,B::RngIntElt) -> SeqEnum
{ Returns traces of Frobenius of the quotient of the Jacobain of genus 3 curve by an elliptic curve at all good primes up to the specified bound. NOTE: does not verify that E is an isogeny factor of Jac(C)! }
    D := Integers()!CurveDiscriminant(C)*Conductor(E);
    P := [p : p in PrimesInInterval(1,B) | not IsDivisibleBy(D,p)];
    return [[p,p+1-#RationalPoints(ChangeRing(C,GF(p))) - TraceOfFrobenius(E,p)] : p in P];
end intrinsic;


/*
    Intrinsics for handling smooth plane quartics of the form y^4 + h(x,z)*y = f(x,z) that are degree-2 covers of genus one curves
    
        y^2 + h(x,z)*y = f(x,z) in [1,2,1] weighted proejctive space.

    We work throughout with Magma's built in support for GenusOneCurve models of degree 2
*/

intrinsic Genus3Curve(m::ModelG1:prec:=100) -> Crv
{ Given a degree 2 genus one model m: y^2 + h(x,z)*y = f(x,z) in [1,2,1]-weighted projective space returns the smooth plane quartic y^4 + h(x,z)*y^2 - f(x,z). }
    require Degree(m) eq 2: "Genus one model must have degree 2.";
    R<x,y,z> := PolynomialRing(BaseRing(m),3);
    if #Eltseq(m) eq 5 then m := GenusOneModel([0,0,0] cat Eltseq(m)); end if;
    return Genus3Curve(Evaluate(DefiningEquation(m),[x,z,y^2]):prec:=prec);
end intrinsic;

intrinsic Genus3Curve(E::CrvEll:prec:=100) -> Crv
{ Given a degree 2 genus one model m: y^2 + h(x,z)*y = f(x,z) in [1,2,1]-weighted projective space returns the smooth plane quartic y^4 + h(x,z)*y^2 - f(x,z). }
    m := GenusOneModel(2,E);
    R<x,y,z> := PolynomialRing(BaseRing(m),3);
    if #Eltseq(m) eq 5 then m := GenusOneModel([0,0,0] cat Eltseq(m)); end if;
    return Genus3Curve(Evaluate(DefiningEquation(m),[x,z,y^2]):prec:=prec);
end intrinsic;

intrinsic Genus3CurveDiscriminant(m::ModelG1) -> Crv
{ Returns the discriminant of the smooth plane quartic y^4 + h(x,z)*y^2 - f(x,z) defined by the degree 2 genus one curve m: y^2 + h(x,z)*y = f(x,z).}
    require Degree(m) eq 2: "Genus one model must have degree 2.";
    a := Eltseq(m);
    if #a eq 5 then return -16*Discriminant(m)^3; end if;
    R<t>:=PolynomialRing(BaseRing(m));
    f := R!a[4..8];
    D := Discriminant(f);
    if Degree(f) eq 3 then D *:= LeadingCoefficient(f)^2; end if;
    return 256*D*Discriminant(m)^2;
end intrinsic;

intrinsic PrymTraces(m::ModelG1,B::RngIntElt) -> SeqEnum
{ Returns traces of Frobenius of abelian surface Prym defined by a degree-2 cover of the specified genus 1 curve up to the specified bound. }
    D := Integers()!Genus3CurveDiscriminant(m);
    P := [p : p in PrimesInInterval(1,B) | not IsDivisibleBy(D,p)];
    C := Genus3Curve(m);
    return [[p,#RationalPoints(Reduction(Jacobian(m),p)) - #RationalPoints(Reduction(C,p))] : p in P];
end intrinsic;

intrinsic PrymTraces(E::CrvEll,B::RngIntElt) -> SeqEnum
{ Returns traces of Frobenius of abelian surface Prym defined by a degree-2 cover of E up to the specified bound. }
    return PrymTraces(GenusOneModel(2,E),B);
end intrinsic;

intrinsic IsGenusOneCover(F::RngMPolElt) -> BoolElt
{ True if F(x,y,z) = y^4 + y^2*h(x,z) + f(x,z) with h, f homogeneous of degree 2,4. }
    R<x,y,z> := Parent(F);
    M := Monomials(F);
    return &and[Degree(m) eq 4 and y^4 in M and IsEven(Degree(m,y)):m in M];
end intrinsic;

intrinsic IsGenusOneCover(C::CrvPln) -> BoolElt
{ True if F(x,y,z) = y^4 + y^2*h(x,z) + f(x,z) with h, f homogeneous of degree 2,4. }
    return IsGenusOneCover(DefiningPolynomial(C));
end intrinsic;

intrinsic GenusOneBase(F::RngMPolElt) -> CrvHyp
{ Given a smooth plane quartic F(x,y,z) = y^4 + h(x,z)y^2 - f(x,z) = 0, returns the genus one curve y^2 + h(x,z)y = f(x,z). }
    require Rank(Parent(F)) eq 3 and Degree(F) eq 4: "Input polynomial should be a homogeneous quartic in three variables.";
    R<x,y,z> := Parent(F);
    M := Monomials(F);
    require &and[Degree(m) eq 4 and y^4 in M and IsEven(Degree(m,y)):m in M]: "Plane quartic must be of they form  y^4 + h(x,z)y^2 - f(x,z).";
    Fc := Coefficients(F);
    i := Index(M,y^4);
    if Fc[i] ne 1 then F := F / Fc[i]; Fc := Coefficients(F); end if;
    h := &+[Parent(F)|Fc[i]*(M[i] div y^2):i in [1..#M]|Degree(M[i],y) eq 2];
    f := - &+[Parent(F)|Fc[i]*M[i]:i in [1..#M]|Degree(M[i],y) eq 0];
    assert y^4 + h*y^2 - f eq F;
    R<X> := PolynomialRing(BaseRing(R));
    return HyperellipticCurve(Evaluate(f,[X,0,1]),Evaluate(h,[X,0,1]));
end intrinsic;

intrinsic GenusOneBase(C::CrvPln) -> CrvHyp
{ Given a smooth plane quartic y^4 + h(x,z)y^2 - f(x,z) = 0, returns the genus one curve y^2 + h(x,z)y = f(x,z). }
    return GenusOneBase(DefiningPolynomial(C));
end intrinsic;

intrinsic GenusTwoPrym(F::RngMPolElt) -> Crvhyp
{ Given a smooth plane quartic F(x,y,z) = y^4 + h(x,z)y^2 - f(x,z)*g(x,z) = 0, with deg(f)=deg(g)=2 attempts to compute a genus 2 curve whose Jacobian is isogenous to the Prym. }
    require false: "Not yet implemented";
end intrinsic;

intrinsic GenusOneModel(a::Tup) -> ModelG1
{ Creates a degree 2 genus one model from the specified tuple of 5 or 8 elements. }
    return GenusOneModel(2, [c:c in a]);
end intrinsic;

intrinsic jInvariant(m::ModelG1) -> FldElt
{ The j-invariant of the Jacobian of the specified non-singular genus one model or . }
    return jInvariant(Jacobian(m));
end intrinsic;

intrinsic HasCM(m::ModelG1) -> BoolElt, RngIntElt
{ Returns boolena indicating whether the Jacobian of the genus one model has CM or not, and if so, the CM discriminant. }
    return HasComplexMultiplication(Jacobian(m));
end intrinsic;

intrinsic HasCM(C::CrvHyp) -> BoolElt, RngIntElt
{ Returns boolena indicating whether the Jacobian of the genus one model specified by C has CM or not, and if so, the CM discriminant. }
    return HasComplexMultiplication(Jacobian(GenusOneModel(C)));
end intrinsic;

intrinsic IsSuperelliptic(C::Crv) -> BoolElt
{ Given a plane curve of the form C:y^m=f(x) returns true, m, f, and false otherwise. }
    if Type(C) eq CrvEll then E:=WeierstrassModel(C); f := HyperellipticPolynomials(E); return true,2,f; end if;
    if Type(C) eq CrvHyp then X:=SimplifiedModel(C); f := HyperellipticPolynomials(X); return true,2,f; end if;
    if Genus(C) eq 0 then return false; end if;
    R<x,y,z>:=PolynomialRing(BaseRing(C),3);
    f := R!DefiningPolynomial(C);
    if BaseRing(Parent(f)) eq Rationals() then d := LCM([Denominator(c):c in Coefficients(f)]); f:= d*f; end if;
    if #[m: m in Terms(f)|Degree(m,y) gt 0] ne 1 then
        f := Evaluate(f,[y,x,z]);
        if #[m: m in Terms(f)|Degree(m,y) gt 0] ne 1 then
            f := Evaluate(f,[x,z,y]);
            if #[m: m in Terms(f)|Degree(m,y) gt 0] ne 1 then
                return false,_,_;
            end if;
        end if;
    end if;
    a := [m:m in Terms(f)|Degree(m,y) gt 0][1];
    if Degree(a,x) gt 0 then 
        f := Evaluate(f,[z,y,x]); a := [m:m in Terms(f)|Degree(m,y) gt 0][1];
        if Degree(a,x) gt 0 then return false,_,_; end if;
    end if;
    R<x>:=PolynomialRing(BaseRing(Parent(f)));
    return true, Degree(a,y), Evaluate(f-a,[x,0,1]);
end intrinsic;

intrinsic RandomizeCurve(C::Crv:B:=3) -> Crv
{ Randomly transorms the curve equation in the hope of avoiding screw cases in period matrix computations. }
    if B eq 0 then return C; end if;
    if Type(C) eq CrvPln then
        return PlaneCurve(RandomizeForm(DefiningPolynomial(C)));
    end if;
    if Type(C) eq CrvHyp then
        g := Genus(C);
        f,h := HyperellipticPolynomials(C);  x := Parent(f).1;
        Rxz<X,Z> := PolynomialRing(BaseRing(f),2);
        f := Homogenization(Evaluate(f,X),Z,2*g+2);  h := h ne 0 select Homogenization(Evaluate(h,X),Z,g+1) else Rxz!0;
        fh := [Evaluate(g,[x,1]): g in RandomizeForms([f,h])];
        return HyperellipticCurve(fh[1], fh[2]);
    end if;
    return C;
end intrinsic;
