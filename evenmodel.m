intrinsic IsEven(f::RngUPolElt) -> BoolElt
{ True if f(x) = f(-x), false otherwise. }
    return f eq Evaluate(f,-Parent(f).1);
end intrinsic;

function transform(f,a,b,c,d)
    R<X,Z> := PolynomialRing(BaseRing(f),2);
    // homogenize to even degree polynomial
    cf := Coefficients(f); n := 2*Ceiling(Degree(f)/2);
    F := &+[cf[i+1]*X^i*Z^(n-i):i in [0..#cf-1]];
    return Evaluate(Evaluate(F,[a*X+b*Z,c*X+d*Z]),[Parent(f).1,1]);
end function;

intrinsic EvenModel(f::RngUPolElt) -> BoolElt, RngUPolElt
{ Given a squarefree polynomial f(x) of deg >= 5 attempts to find an even polynomial g(x) that whose homogenization is GL2-equivalent to that of f
(meaning that G(X,Z) = F(a*X+b*Z,c*X+d*Z) for some invertible matrix [[a,b],[c,d]], where G and F are the homogenizations of g and f). }
    if IsEven(f) then return true,f; end if;
    K := BaseRing(f);
    x := Parent(f).1;
    // Get automorphism group of y^2=f(x), this will fail if f(x) is not squarefree and of degree at least 5, or if char(K)=2
    G, phi := AutomorphismGroupOfHyperellipticCurve(f : explicit := true);
    sts := false;
    for g in G do
        if Order(g) ne 2 then continue; end if;
        a,b,c,d := Explode(Eltseq(phi(g)[1]));
        if c eq 0 and a eq d then continue; end if; // involutio with c=0 and a=d must have b=0
        sts := true;
        break;
    end for;
    if not sts then return false,_; end if;
    if c eq 0 then
        // nonscalar involution x -> (a/d)x + b/d satisfies (a/d)^2*x + (a/d)(b/d) + (b/d) = x, so a=-d
        // this fixes infinity=(1:0) and -b/(2*d)
        // applying the transformation x -> x + b/(2*d) will keep infinty fixed and move the second fixed point to zero
        g := transform(f,1,b/(2*d),0,1);
        assert IsEven(g);
    else
        // Solve cx^2 + (d-a)x - b = 0 to find fixed points
        disc := (d-a)^2 + 4*b*c;
        is_square, r := IsSquare(K!disc);
        if not is_square then return false,_; end if;
        p := ((a-d)+r)/(2*c); q := ((a-d)-r)/(2*c); // fixed points
        // moving fixed points to 0 and infinty via x -> (x-p)/(x-q) yields -1
        g := transform(f,-p,q,-1,1);
    end if;
    assert IsEven(g);
    // make g integral if we are over Q
    if K eq Rationals() then
        d := LCM([Denominator(c):c in Coefficients(g)]);
        g *:= d^2;
    end if;
    return true,g;
end intrinsic;

intrinsic EvenModel(C::CrvHyp) -> BoolElt, CrvHyp
{ Attempts to transform the genus 3 hyperelliptic curve C to a model of the form y^2 = f(x^2), returns a boolean and the transformed model, if found. }
    f := HyperellipticPolynomials(SimplifiedModel(C));
    b,g := EvenModel(f);
    if b then return b,HyperellipticCurve(g); else return b,_; end if;
end intrinsic;
