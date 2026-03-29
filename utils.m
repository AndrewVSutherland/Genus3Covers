//freeze;
/*
    General purpose utilities (often things I wished Magma supported directly) and aliases/wrappers for Magma functions to make them easer for me to use and/or remember.

    Copyright (c) Andrew V. Sutherland, 2019-2024.  See License file for details on copying and usage.
*/

declare verbose ParallelJobs, 1;

intrinsic ProfileTimes(:All:=false) -> SeqEnum
{ Lists vertices in profile graph in order of time.  You need to SetProfile(true), run something, then call this (which will SetProfile(false) before dumping). }
    SetProfile(false);
    return S where S := Sort([Label(V!i):i in [1..#V]|All or (r`Count gt 0 and r`Time gt 0.01 where r:=Label(V!i))] where V:=Vertices(ProfileGraph()),func<a,b|a`Time-b`Time>);
end intrinsic;

intrinsic PrintProfile(:All:=false)
{ Lists vertices in profile graph in order of time.  You need to SetProfile(true), run something, then call this (which will SetProfile(false) before dumping). }
    S := ProfileTimes(:All:=All);
    for r in S do printf "%.3os in %o calls to %o\n",r`Time,r`Count,r`Name; end for;
end intrinsic;

intrinsic Factorization(r::FldRatElt) -> SeqEnum
{ The prime factorization of the rational number r. }
    return Sort(Factorization(Numerator(r)) cat [<a[1],-a[2]>:a in Factorization(Denominator(r))]);
end intrinsic;

intrinsic GSp(d::RngIntElt, q::RngIntElt) -> GrpMat
{ The group of symplectic similitudes of degree d over F_q. }
    return CSp(d,q);
end intrinsic;

intrinsic PlaneCurve(f::RngMPolElt) -> CrvPln
{ The curve in P^2 defined by f(x,y,z) = 0. }
    require Rank(Parent(f)) eq 3: "Input should be a polynomial in three variables.";
    return Curve(ProjectiveSpace(Parent(f)),f);
end intrinsic;

intrinsic PlaneCurve(c::SeqEnum) -> CrvPln
{ The curve in P^2 defined by f(x,y,z) = 0, where f is specified as a list of binom(d+2,2) coefficients (in lex order matching MonomialsOfDegree so that c eq Coefficients(PlaneCurve(c)) holds). }
    d := Floor(Sqrt(2*#c))-1;
    require d gt 1 and #c  eq Binomial(d+2,2): "Then length of the input must be of the form binom(d+2,2) with d > 1.";
    M := MonomialsOfDegree(PolynomialRing(Parent(c[1]),3),d);  assert #M eq #c;
    return PlaneCurve(&+[c[i]*M[i]:i in [1..#c]]);
end intrinsic;

intrinsic Eltseq(s::SetMulti[RngIntElt]) -> SeqEnum
{ Sorted sequence of tuples representing a multiset of integers. }
    return Sort([<n,Multiplicity(s,n)>:n in Set(s)]);
end intrinsic;

intrinsic ReplaceCharacter(s::MonStgElt,c::MonStgElt,d::MonStgElt) -> MonStgElt
{ Efficiently replace every occurrence of the character c in s with the string d (c must be a single character but d need not be). This should be used as an alternative to SubstituteString, which scales non-linearly. }
    require #c eq 1: "The second parameter must be a single character (string of length 1).";
    t := Split(s,c:IncludeEmpty);
    if s[#s] eq c then Append(~t,""); end if; // add empty string at the end which Split omits
    return Join(t,d);
end intrinsic;

intrinsic ReplaceString(s::MonStgElt,c::MonStgElt,d::MonStgElt) -> MonStgElt
{ Greedily replace each occurrence of string c in s with the string d. This is a completely naive unoptimized implementation, but it still outperforms SubstituteString for large strings. }
    require #c ge 1: "The string to be replaced cannot be empty.";
    m := #c;
    t := "";
    n := Index(s,c);
    while n gt 0 do
        t cat:= s[1..n-1] cat d;
        s := s[n+m..#s];
        n := Index(s,c);
    end while;
    return t cat s;
end intrinsic;

intrinsic djb2(s::MonStgElt:b:=64) -> RngIntElt
{ Returns the b-bit djb2 hash of s. Default value of b is 64. }
    h:=5381; m:=2^b-1; s := BinaryString(s);
    for i:=1 to #s do h := BitwiseAnd(33*h+s[i],m); end for;
    return h;
end intrinsic;

intrinsic PySplit(s::MonStgElt, sep::MonStgElt : limit:=-1) -> SeqEnum[MonStgElt]
{Splits using Python semantics (different when #sep > 1, and different when sep at beginning or end)}
    if #sep eq 0 then
        error "Empty separator";
    end if;
    i := 1;
    j := 0;
    ans := [];
    while limit gt 0 or limit eq -1 do
        if limit ne -1 then limit -:= 1; end if;
        pos := Index(s, sep, i);
        if pos eq 0 then break; end if;
        j := pos - 1;
        Append(~ans, s[i..j]);
        i := j + #sep + 1;
    end while;
    Append(~ans, s[i..#s]);
    return ans;
end intrinsic;

intrinsic split(s::MonStgElt,d::MonStgElt) -> SeqEnum[MonStgElt]
{ Splits the string s using the delimter d, including empty and trailing elements (equivalent to python r.split(d) in python). }
    return Split(s,d:IncludeEmpty) cat (s[#s] eq d select [""] else []);
end intrinsic;

intrinsic getrecs(filename::MonStgElt:Delimiter:=":") -> SeqEnum[SeqEnum[MonStgElt]]
{ Reads a delimited file, returns list of lists of strings (one list per line). }
    return [split(r,Delimiter):r in Split(Read(filename))];
end intrinsic;

intrinsic putrecs(filename::MonStgElt,S::SeqEnum[SeqEnum[MonStgElt]]:Delimiter:=":")
{ Given a list of lists of strings, creates a colon delimited file with one list per line. }
    fp := Open(filename,"w");
    n := 0;
    for r in S do Puts(fp,Join(r,Delimiter)); n+:=1; end for;
    Flush(fp);
end intrinsic;

intrinsic maxcerts (S::SetEnum, Ts::SeqEnum[SetEnum]:Limit:=3) -> SeqEnum[SetEnum]
{ Given a set S and a list of subsets T of S, returns a list of minimal subsets of S of cardinality at most Limit that are not contained in any of the T. This can be viewed as the floor of the lattice of subsets of S that not contained in any T. }
    X := &join[S diff T : T in Ts];
    A := [];
    for i:=1 to Limit do
        A cat:= [s:s in Subsets(X,i) | &and[not t subset s: t in A] and &and[not s subset T : T in Ts]];
    end for;
    return A;
end intrinsic;

intrinsic StringToStrings (s::MonStgElt) -> SeqEnum[MonStgElt]
{ Given a string encoding a list of strings that do not contain commas or whitespace, e.g. "[cat,dog]", returns a list of the strings, e.g [ "cat", "dog" ]. }
    s := StripWhiteSpace(s);
    require s[1] eq "[" and s[#s] eq "]": "Input must be a string representing a list";
    s := s[2..#s-1];
    return Split(s,",");
end intrinsic;

intrinsic sum(X::[]) -> .
{ Sum of a sequence (empty sum is 0). }
    if #X eq 0 then
        try
            return Universe(X)!0;
        catch e
            return Integers()!0;
        end try;
    end if;
    return &+X;
end intrinsic;

intrinsic sum(v::ModTupRngElt) -> .
{ Sum over a vector. }
    return  sum(Eltseq(v));
end intrinsic;

intrinsic prod(X::[]) -> .
{ Product of a sequence (empty product is 1). }
    if #X eq 0 then
        try
            return Universe(X)!1;
        catch e
            return Integers()!1;
        end try;
    end if;
    return &*X;
end intrinsic;

intrinsic prod(v::ModTupRngElt) -> .
{ Product of a vector. }
    return prod(Eltseq(v));
end intrinsic;

intrinsic strip(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; used to be faster than StripWhiteSpace, now that StripWhiteSpace is faster we just call it. }
    return StripWhiteSpace(X);
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end intrinsic;

intrinsic atoi(s::MonStgElt) -> RngIntElt
{ Converts a string to an integer (alias for StringToInteger). }
    return #s gt 0 select StringToInteger(s) else 0;
end intrinsic;

intrinsic itoa(n::RngIntElt) -> MonStgElt
{ Converts an integer to a string (equivalent to but slightly slower than IntegerToString, faster than sprint). }
    return IntegerToString(n);
end intrinsic;

intrinsic StringToReal(s::MonStgElt) -> RngIntElt
{ Converts a decimal string (like 123.456 or 1.23456e40 or 1.23456e-10) to a real number at default precision. }
    if #s eq 0 then return 0.0; end if;
    if "e" in s then
        t := Split(s,"e");
        require #t eq 2: "Input should have the form 123.456e20 or 1.23456e-10";
        return StringToReal(t[1])*10.0^StringToInteger(t[2]);
    end if;
    t := Split(s,".");
    require #t le 2: "Input should have the form 123 or 123.456 or 1.23456e-10";
    n := StringToInteger(t[1]);  s := t[1][1] eq "-" select -1 else 1;
    return #t eq 1 select RealField()!n else RealField()!n + s*RealField()!StringToInteger(t[2])/10^#t[2];
end intrinsic;

intrinsic atof (s::MonStgElt) -> RngIntElt
{ Converts a decimal string (like "123.456") to a real number at default precision. }
    return StringToReal(s);
end intrinsic;

intrinsic StringsToAssociativeArray(s::SeqEnum[MonStgElt]) -> Assoc
{ Converts a list of strings "a=b" to an associative array A with string keys and values such that A[a]=b. Ignores strings not of the form "a=b". }
    A := AssociativeArray(Universe(["string"]));
    for a in s do t:=Split(a,"="); if #t eq 2 then A[t[1]]:=t[2]; end if; end for;
    return A;
end intrinsic;

intrinsic atod(s::SeqEnum[MonStgElt]) -> Assoc
{ Converts a list of strings "a=b" to an associative array A with string keys and values such that A[a]=b (alias for StringsToAssociativeArray). }
    return StringsToAssociativeArray(s);
end intrinsic;

intrinsic StringToIntegerArray(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Given string representing a sequence of integers, returns the sequence (faster and safer than eval). }
    t := strip(s);
    if t eq "[]" then return [Integers()|]; end if;
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic atoii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of integers (alias for StringToIntegerArray). }
    return StringToIntegerArray(s);
end intrinsic;

intrinsic iitoa(a::SeqEnum[RngIntElt]) -> MonStgElt
{ Converts a sequence of integers to a string (faster than sprint). }
    return "[" cat Join([IntegerToString(n) : n in a],",") cat "]";
end intrinsic;

intrinsic atoiii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of integers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    assert #t gt 4;
    if t[1..2] eq "[<" and t[#t-1..#t] eq ">]" then
        r := Split(t[2..#t-1],"<");
        return [[Integers()|StringToInteger(n):n in Split(a[1] eq ">" select "" else Split(a,">")[1],",")]:a in r];
    elif t[1..2] eq "[[" and t[#t-1..#t] eq "]]" then
        r := Split(t[2..#t-1],"[");
        return [[Integers()|StringToInteger(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
    else
        error "atoiii: Unable to parse string " cat s;
    end if;
end intrinsic;

intrinsic atoiiii(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of sequences of integers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    if t eq "[[[]]]" then return [[[Integers()|]]]; end if;
    assert #t gt 5 and t[1..3] eq "[[[" and t[#t-2..#t] eq "]]]";
    s := s[2..#s-1];
    a := [];
    while true do
        i := Index(s,"]],[[");
        if i eq 0 then Append(~a,atoiii(s)); break; end if;
        Append(~a,atoiii(s[1..i+1]));
        s := s[i+3..#s];
    end while;
    return a;
end intrinsic;

intrinsic StringToRationalArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of rational numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [StringToRational(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic StringToRealArray(s::MonStgElt) -> SeqEnum[RatFldElt]
{ Given string representing a sequence of real numbers, returns the sequence (faster and safer than eval). }
    if s eq "[]" then return []; end if;
    t := strip(s);
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [atof(n):n in Split(t[2..#t-1],",")];
end intrinsic;

intrinsic atoff(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of reals (alias for StringToRealArray). }
    return StringToRealArray(s);
end intrinsic;

intrinsic atofff(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of real numbers. }
    t := strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[RealField()|]]; end if;
    assert #t gt 4 and t[1..2] eq "[[" and t[#t-1..#t] eq "]]";
    r := Split(t[2..#t-1],"[");
    return [[RealField()|StringToReal(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
end intrinsic;

intrinsic goodp(f::RngUPolElt,p::RngIntElt) -> RngIntElt
{ Returns true if the specified polynomial is square free modulo p (without computing the discrimnant of f). }
    return Discriminant(PolynomialRing(GF(p))!f) ne 0;
end intrinsic;

intrinsic Base26Encode(n::RngIntElt) -> MonStgElt
{ Given a nonnegative integer n, returns its encoding in base-26 (a=0,..., z=25, ba=26,...). }
    require n ge 0: "n must be a nonnegative integer";
    alphabet := "abcdefghijklmnopqrstuvwxyz";
    s := alphabet[1 + n mod 26]; n := (n-(n mod 26)) div 26;
    while n gt 0 do
        s := alphabet[1 + n mod 26] cat s; n := (n-(n mod 26)) div 26;
    end while;
    return s;
end intrinsic;

intrinsic Base26Decode(s::MonStgElt) -> RngIntElt
{ Given string representing a nonnegative integer in base-26 (a=0,..., z=25, ba=26,...) returns the integer. }
    alphabetbase := StringToCode("a");
    n := 0;
    for c in Eltseq(s) do n := 26*n + StringToCode(c) - alphabetbase; end for;
    return n;
end intrinsic;

// This implementation is slow and suitable only for small groups
intrinsic PolycyclicPresentation(gens::SeqEnum,m::UserProgram,id::.) -> SeqEnum[RngIntElt], Map
{ Given a sequence of generators in a uniquely represented hashable polycyclic group with composition law m and identity element id, returns sequence of relative orders and a map from group elements to exponent vectors.}
    r := [Integers()|];
    if #gens eq 0 then return r, func<a|r>; end if;
    n := #gens;
    T := [Universe(gens)|id];
    while true do g := m(T[#T],gens[1]); if g eq id then break; end if; Append(~T,g); end while;
    Append(~r,#T);
    for i:=2 to n do
        X := Set(T); S := T; j := 1;
        g := gens[i];  h := g; while not h in X do S cat:= [m(t,h):t in T]; h := m(h,g); j +:= 1; end while;
        Append(~r,j);  T := S;
    end for;
    ZZ := Integers();
    A := AssociativeArray(Universe(gens));
    for i:=1 to #T do A[T[i]] := i-1; end for;
    rr := [ZZ|1] cat [&*r[1..i-1]:i in [2..n]];
    return r, func<x|[Integers()|(e div rr[i]) mod r[i] : i in [1..n]] where e:=A[x]>;
end intrinsic;

intrinsic OrderStats(G::Grp) -> SetMulti[RngIntElt]
{ Multiset of order statistics of elements of the group G. }
    if #G eq 1 then return {*1*}; end if;
    if IsAbelian(G) then
        function pos(p,a)
            s := Multiset(a);  n := Round(Log(p,a[#a]));
            t:= [1] cat [&*[Integers()|n:n in a|n lt p^i] * &*[Integers()|p^Multiplicity(s,r):r in Set(s)|r ge p^i]^i:i in [1..n]];
            return [[1,1]] cat [[p^i,t[i+1]-t[i]]:i in [1..#t-1]];
        end function;
        G := AbelianGroup(G);
        Z := [pos(p,pPrimaryInvariants(G,p)):p in PrimeDivisors(#G)];
        return {* &*[r[1]:r in x]^^&*[r[2]:r in x] : x in CartesianProduct(Z) *};
    end if;
    C:=ConjugacyClasses(G);
    return SequenceToMultiset(&cat[[c[1]:i in [1..c[2]]]:c in C]);
end intrinsic;

intrinsic CyclicGenerators(G::GrpAb) -> SeqEnum[GrpAb]
{ A list of generators of the distinct cyclic subgroups of the finite abelian group G. }
    require IsFinite(G): "G must be finite.";
    if #G eq 1 then return [Identity(G)]; end if;
    if #Generators(G) eq 1 then g := G.1; return [e*g:e in Reverse(Divisors(Exponent(G)))]; end if;
    X := [[Identity(G)] cat &cat[[H`subgroup.1: H in Subgroups(Gp:Sub:=[n])]:n in Reverse(Divisors(Exponent(Gp)))|n gt 1] where Gp:=SylowSubgroup(G,p):p in PrimeDivisors(Exponent(G))];
    return [&+[z[i]:i in [1..#z]]:z in CartesianProduct(X)];
end intrinsic;

intrinsic ConjugateIntersection(G::Grp, H1::Grp, H2::Grp) -> Grp
{ Given finite subgroups H1 and H2 of a group G, returns a largest subgroup of G contained in a conjugate of H1 and a conjugate of H2. }
    S := [H1 meet H:H in Conjugates(G,H2)];
    I := [<Index(G,S[i]),i>:i in [1..#S]];
    return S[Min(I)[2]];
end intrinsic;
    
intrinsic ConjugateCompositum(G::Grp, H1::Grp, H2::Grp) -> Grp
{ Given subgroups H1 and H2 of G, returns a smallest subgroup of G that contains a conjugate of H1 and a conjugate of H2. }
    S := [sub<G|H1,H>:H in Conjugates(G,H2)];
    I := [<#S[i],i>:i in [1..#S]];
    return S[Min(I)[2]];
end intrinsic;

intrinsic getval(X::Any,k::Any:missing:=[]) -> Any
{ Returns X[k] if it is defined and [] (or whatever the optional argument missing is set to) otherwise (analog of the get method in Python). }
    return b select v else missing where b,v := IsDefined(X,k);
end intrinsic;

intrinsic IndexFibers (S::SeqEnum, f::UserProgram : Unique:=false, Project:=false) -> Assoc
{ Given a list of objects S and a function f on S creates an associative array satisfying A[f(s)] = [t:t in S|f(t) eq f(s)]. }
    A := AssociativeArray();
    if Type(Project) eq UserProgram then
        if Unique then for x in S do A[f(x)] := Project(x); end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),Project(x)); end for;
    else
        if Unique then for x in S do A[f(x)] := x; end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),x); end for;
    end if;
    return A;
end intrinsic;

intrinsic IndexFibers (S::List, f::UserProgram : Unique:=false, Project:=false) -> Assoc
{ Given a list of objects S and a function f on S creates an associative array satisfying A[f(s)] = [t:t in S|f(t) eq f(s)]. }
    A := AssociativeArray();
    if Type(Project) eq UserProgram then
        if Unique then for x in S do A[f(x)] := Project(x); end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),Project(x)); end for;
    else
        if Unique then for x in S do A[f(x)] := x; end for; return A; end if;
        for x in S do y := f(x); A[y] := Append(getval(A,y),x); end for;
    end if;
    return A;
end intrinsic;

intrinsic IndexFile (filename::MonStgElt, key::. : Delimiter:=":", Unique:=false, data:=[]) -> Assoc
{ Loads file with colon-delimited columns (or as specified by Delimiter) creating an AssociativeArray with key specified by keys (a column index or list of column indexes) and contents determined by data, which should be either a column index or list of column indexes (empty list means entire record). }
    require Type(key) eq RngIntElt or Type(key) eq SeqEnum: "second parameter should be a column index or list of column indices";
    if Type(data) eq RngIntElt then data := [data]; end if;
    if #data eq 1 then Project := func<r|r[data[1]]>; else if #data gt 1 then Project := func<r|r[data]>; else Project := func<r|r>; end if; end if;
    return IndexFibers(getrecs(filename), func<r|r[key]> : Unique:=Unique, Project:=Project);
end intrinsic;

intrinsic ReduceToReps (S::[], E::UserProgram: min:=func<a,b|a>) -> SeqEnum
{ Given a list of objects S and an equivalence relation E on S returns a maximal sublist of inequivalent objects. }
    if #S le 1 then return S; end if;
    if #S eq 2 then return E(S[1],S[2]) select [min(S[1],S[2])] else S; end if;
    T:=[S[1]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added entries first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j]) then T[j]:=min(s,T[j]); sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,s); end if;
    end for;
    return T;
end intrinsic;

intrinsic Classify (S::[], E::UserProgram) -> SeqEnum[SeqEnum]
{ Given a list of objects S and an equivalence relation E on them returns a list of equivalence classes (each of which is a list). }
    if #S eq 0 then return []; end if;
    if #S eq 1 then return [S]; end if;
    if #S eq 2 then return E(S[1],S[2]) select [S] else [[S[1]],[S[2]]]; end if;
    T:=[[S[1]]];
    for i:=2 to #S do
        s:=S[i]; sts:=true;
        for j:=#T to 1 by -1 do // check most recently added classes first in case adjacent objects in S are more likely to be equivalent (often true)
            if E(s,T[j][1]) then T[j] cat:= [s]; sts:=false; break; end if;
        end for;
        if sts then T:=Append(T,[s]); end if;
    end for;
    return T;
end intrinsic;

intrinsic DihedralGroup(G::GrpAb) -> Grp
{ Construct the generalized dihedral group dih(G) := G semidirect Z/2Z with Z/2Z acting by inversion. }
    Z2 := AbelianGroup([2]);
    h:=hom<Z2->AutomorphismGroup(G)|x:->hom<G->G|g:->IsIdentity(x) select g else -g>>;
    return SemidirectProduct(G,Z2,h);
end intrinsic;

intrinsic Quotients(G::Grp:Order:=0) -> SeqEnum
{ Returns a list of quotients of G (either all non-trivial quotients or those of the specified Order). }
    n := #G;
    return [quo<G|H> where H:=K`subgroup : K in NormalSubgroups(G) | (Order eq 0 and not #K`subgroup in [1,n]) or Index(G,K`subgroup) eq Order];
end intrinsic;

function TransformForm(f, T : co := true, contra := false)
    R := Parent(f);
    vars := Matrix([ [ mon ] : mon in MonomialsOfDegree(R, 1) ]);
    if (not co) or contra then
        return Evaluate(f, Eltseq(ChangeRing(Transpose(T)^(-1), R) * vars));
    end if;
    return Evaluate(f, Eltseq(ChangeRing(T, R) * vars));
end function;

function RandomInvertibleMatrix(R, B)
    assert B ge 1;
    n := Rank(R); F := BaseRing(R);
    D := [ -B..B ];
    repeat T := Matrix(F, n, n, [ Random(D) : i in [1..n^2] ]); until IsUnit(Determinant(T));
    return T;
end function;

intrinsic RandomizeForm(f::RngMPolElt: B:=3) -> RngMPolElt
{ Applies a random invertible linear change of variables to the specified homogeneous polynomial (preserves integrality). }
    require IsHomogeneous(f): "Input polynomial must be homogeneous";
    return TransformForm(f, RandomInvertibleMatrix(Parent(f), B));
end intrinsic;

intrinsic RandomizeForms(forms::SeqEnum[RngMPolElt]: B:=3) -> SeqEnum[RngMPolElt]
{ Applies a random invertible linear change of variables to the specified sequence of homogeneous polynomials (preserves integrality). }
    require &and[IsHomogeneous(f) : f in forms]: "Input polynomial must be homogeneous";
    if #forms eq 0 then return forms; end if;
    M := RandomInvertibleMatrix(Parent(forms[1]),B);
    return [TransformForm(f, M) : f in forms];
end intrinsic;

intrinsic MinimizeGenerators(G::Grp) -> Grp
{ Given a finite group G tries to reduce the number of generators by sampling random elements.  Result is not guaranteed to minimize the number of generators but this is very likely. }
    require IsFinite(G): "G must be a finite group";
    n := #G;
    if IsAbelian(G) then
        Gab,pi := AbelianGroup(G);
        B := AbelianBasis(Gab);
        return sub<G|[Inverse(pi)(b):b in B]>;
    end if;
    r := 2;
    while true do
        for i:=1 to 100 do H := sub<G|[Random(G):i in [1..r]]>; if #H eq n then return H; end if; end for;
        r +:= 1;
    end while;
end intrinsic;

intrinsic RegularRepresentation(H::Grp) -> GrpPerm
{ The regular representation of H as a permutation group of degree #H. }
    _,H := RegularRepresentation(H,sub<H|>);
    return H;
end intrinsic;

intrinsic HurwitzClassNumber(N::RngIntElt) -> FldRatElt
{ The Hurwitz class number of positive definite binary quadratic forms of discriminant -N with each class C counted with multiplicity 1/#Aut(C), extended by Zagier to H(0)=-1/12 and H(-u^2)=-u/2, with H(-n) = 0 for all nonsquare n>0. }
    if N eq 0 then return -1/12; end if; if N lt 0 then b,u:=IsSquare(N); return b select -u/2 else 0;  end if;
    if not N mod 4 in [0,3] then return 0; end if;
    D := FundamentalDiscriminant(-N); f := Integers()!Sqrt(-N/D); w := D lt -4 select 1 else (D lt -3 select 2 else 3);
    return ClassNumber(D)/w * &+[MoebiusMu(d)*KroneckerSymbol(D,d)*SumOfDivisors(f div d):d in Divisors(f)];
end intrinsic;

intrinsic KroneckerClassNumber(D::RngIntElt) -> RngIntElt
{ The sum of the class numbers of the discriminants DD that divide the given imaginary quadratic discriminant D (this is not the same as the Hurwitz class number of -D, in particular, it is always an integer). }
    require D lt 0 and IsDiscriminant(D): "D must be an imaginary quadratic discriminant.";
    D0 := FundamentalDiscriminant(D);
    if D0 lt -4 then return HurwitzClassNumber(-D); end if;
    _,f := IsSquare(D div D0);
    return &+[ClassNumber(d^2*D0): d in Divisors(f)];
end intrinsic;

intrinsic split(f::RngUPolElt, p::RngIntElt) -> SetMulti
{ The multiset of pairs <d,e> where d is the residue field degree and e is the ramification index of the primes above p in the number field defined by the monic irreducible polynomial f. }
    require IsMonic(f) and IsIrreducible(f): "The polynomial f must be irreducible.";
    require IsPrime(p): "p must be a rational prime.";
    s := Pipe(Sprintf("sage -c \"load('/home/drew/Dropbox/magma/split.py'); print(split(%o,%o))\"",Coefficients(f),p),"");
    try
        s := eval(s);
        return {* <a[1],a[2]>: a in s *};
    catch e
        error "Call to Sage failed with return value: " cat s;
    end try;
end intrinsic;

function plog(p,e,a,b) // returns nonnegative integer x such that a^x = b or -1, assuming a has order p^e
    if e eq 0 then return a eq 1 and b eq 1 select 0 else -1; end if;
    if p^e le 256 then return Index([a^n:n in [0..p^e-1]],b)-1; end if;
    if e eq 1 then // use BSGS for groups of prime order, this is the base case of the recursion
        aa := Parent(a)!1;
        r := Floor(Sqrt(p)); s := Ceiling(p/r);
        babys := AssociativeArray(); for x:=0 to r-1 do babys[aa] := x; aa *:= a; end for;
        bb := b;
        x := 0; while x lt s do if IsDefined(babys,bb) then return (babys[bb]-r*x) mod p; end if; bb *:= aa; x +:=1; end while;
        return -1;
    end if;
    e1 := e div 2; e0 := e-e1;
    x0 := $$(p,e0,a^(p^e1),b^(p^e1)); if x0 lt 0 then return -1; end if;
    x1 := $$(p,e1,a^(p^e0),b*a^(-x0)); if x1 lt 0 then return -1; end if;
    return x0 + p^e0*x1;
end function;

intrinsic Log (a::RngIntResElt, b::RngIntResElt) -> RngIntElt
{ Given a,b in (Z/nZ)*, returns least nonnegative x such that a^x = b or -1 if no such x exists. }
    R := Parent(a); n := #R;
    require Parent(b) eq R: "Arguments must be elements of the same ring Z/nZ";
    m := Order(a); if m le 5000 then return Index([a^n:n in [0..m-1]],b)-1; end if;
    P := Factorization(n);
    M := [Order(Integers(p[1]^p[2])!a) : p in P];
    function qlog(p,e,m,a,b) // computes discrete log of b wrt a in Z/p^eZ given the order m of a
        R := Integers(p^e); a := R!a; b := R!b;
        if p eq 2 then return plog(2,Valuation(m,2),a,b); end if;
        me := Valuation(m,p);  m1 := p^me; m2 := GCD(m,p-1);
        x1 := plog(p,me,a^m2,b^m2); if x1 lt 0 then return x1; end if;
        x2 := Log(GF(p)!(a^m1),GF(p)!(b^m1)); if x2 lt 0 then return x2; end if;
        return CRT([x1,x2],[m1,m2]);
    end function;
    L := [qlog(P[i][1],P[i][2],M[i],a,b) : i in [1..#P]];
    if -1 in L then return -1; end if;
    return CRT(L,M);
end intrinsic; 

intrinsic MinimalContractions(p::SetMulti[RngIntElt]) -> SetEnum[SetMulti[RngIntElt]]
{ Given a multiset p of integers representing a partititon of n with k blocks, returns the set of partitions of n with k-1 blocks of which p is a refinement. }
    if #p le 1 then return {Parent(p)|}; end if;
    return {Include(Exclude(Exclude(p,a),b),a+b):a,b in Set(p)|a ne b or Multiplicity(p,a) gt 1};
end intrinsic;

intrinsic Contractions(p::SetMulti[RngIntElt],k::RngIntElt) ->  SetEnum[SetMulti[RngIntElt]]
{ Given a multiset p of integers representing a partititon of n, returns the set of partitions of n with k blocks of which p is a refinement. }
    if #p lt k then return {}; end if;
    if #p eq k then return {p}; end if;
    P := {p};
    for i:=k+1 to #p do P := &join[MinimalContractions(p):p in P]; end for;
    return P;
end intrinsic;

intrinsic Contractions(p::SetMulti[RngIntElt]) ->  SetEnum[SetMulti[RngIntElt]]
{ Given a multiset p of integers representing a partititon of n, returns the set of partitions of n of which p is a refinement. }
    P := {p}; Q := P;
    for i:=1 to #p-1 do Q := &join[MinimalContractions(p):p in Q]; P join:= Q; end for;
    return P;
end intrinsic;

intrinsic CommonContractions(S::SeqEnum[SetMulti[RngIntElt]]) -> SetEnum[SetMulti[RngIntElt]]
{ Given a sequence of multisets p of integers representing a partititon of n, returns the set of partitions of n that are refined by every element of S. }
    require #{&+p:p in S} eq 1: "Incompatible partitions.";
    return &meet[Contractions(p):p in S];
end intrinsic;

intrinsic MinimalCommonContractions(S::SeqEnum[SetMulti[RngIntElt]]) -> SetEnum[SetMulti[RngIntElt]]
{ Given a sequence of multisets of integers representing partitions of some integer n, returns the set T of partitions of n with k blocks that are refined by every member of S with k maximized subject to ensuring T is non-empty.  Note that there may be partitions with less than k blocks that are refined by every element of S but not by any element of T. }
    if #S eq 1 then return Set(S); end if;
    require #{&+p:p in S} eq 1: "Incompatible partitions.";
    S := Sort(S,func<a,b|#a-#b>);
    k := #S[1];
    if k eq 1 then return S[1]; end if;
    P := {S[1]};
    for i:=2 to #S do
        Q := Contractions(S[i],k);
        R := P meet Q;
        while #R eq 0 do
            k -:= 1;
            if k eq 1 then return {{*&+S[1]*}}; end if;
            P := &join[MinimalContractions(p):p in P];
            Q := &join[MinimalContractions(p):p in Q];
            R := P meet Q;
        end while;
        P := R;
    end for;
    return P;
end intrinsic;


/*
This code should work but does not due to bugs in Magma's integer LP code (in addition to displaying spurious error messages, it occasionally claims no solution exists when it does).

To reproduce these problems:

for a,b in Partitions(12) do if IsRefinement(a,b) ne (Multiset(a) in Contractions(Multiset(b))) then print a,b; assert false; end if; end for;

intrinsic IsRefinement(p::SeqEnum[RngIntElt],q::SeqEnum[RngIntElt]) -> BoolElt
{ True if q is a refinement of the integer partition p. }
    require &+p eq &+q: "Incompatible partitions.";
    if p eq q then return true; end if;
    LHS := []; RHS:=[];
    np := #p; nq := #q; m := np*nq;
    // We use #p*#q binary variables x_{ij} with i ranging over blocks p_i of p and j ranging over blocks q_j of q
    // We require sum_j x_{ij}*q_j = p_i for all i (writing p_i as the sum of the q_j for which x_ij=1)
    // We require sum_i x_{ij} = 1 for all j (each q_j is included in the sum for exactly one p_i)
    // There are thus #p+#q relations
    z := [Integers()|0:i in [1..m]];
    for i:=0 to np-1 do
        r := z;
        for j:=0 to nq-1 do r[nq*i+j+1] := q[j+1]; end for;
        Append(~LHS,r); Append(~RHS,[p[i+1]]);
    end for;
    for j:=0 to nq-1 do
        r := z;
        for i:=0 to np-1 do r[nq*i+j+1] := 1; end for;
        Append(~LHS,r); Append(~RHS,[1]);
    end for;
    v,s := MinimalZeroOneSolution(Matrix(LHS),Matrix([[0]:i in [1..np+nq]]),Matrix(RHS),Matrix([[1:i in [1..m]]]));
    return s eq 0;
end intrinsic;

intrinsic IsRefinement(p::SetMulti[RngIntElt],q::SetMulti[RngIntElt]) -> BoolElt
{ True if q is a refinement of the integer partition p. }
    return IsRefinement([n:n in p],[n:n in q]);
end intrinsic;
*/

intrinsic C4C6Invariants(E::CrvEll[FldRat]) -> RngInt, RngInt
{ Returns the c4 and c6 invariants of the specified elliptic curve E/Q (assumes E is defined by an integral model). }
    a := Coefficients(E);
    b2 := a[1]^2+4*a[2];
    b4 := a[1]*a[3]+2*a[4];
    b6 := a[3]^2+4*a[5];
    b8 := a[1]^2*a[5] - a[1]*a[3]*a[4] + 4*a[2]*a[5] + a[2]*a[3]^2 - a[4]^2;
    c4 := b2^2-24*b4;
    c6 := -b2^3+36*b2*b4-216*b6;
    return Integers()!(b2^2-24*b4),Integers()!(-b2^3+36*b2*b4-216*b6);
end intrinsic;

intrinsic GetFilenames(I::Intrinsic) -> SeqEnum
{ Return the filenames where such intrinsics are defined }
    lines := Split(Sprint(I, "Maximal"));
    res := [];
    def := "Defined in file: ";
    for i->line in lines do
        p := Position(line, ")");
        if line[1] eq "(" and p ne 0 then
            // figure out filename
            if i gt 1 and #lines[i-1] ge #def and lines[i-1][1..#def] eq def then
                comma := Position(lines[i-1], ",");
                filename := lines[i-1][#def + 1..comma-1];
            else
                filename := "";
            end if;
            arguments := [Split(elt, ":")[2] : elt in Split(StripWhiteSpace(line[2..p-1]), ",")];
            s := Split(StripWhiteSpace(line), "->");
            if #s eq 1 then
                values := [];
            else
                assert #s eq 2;
                values := Split(StripWhiteSpace(s[2]), ",");
            end if;
            Append(~res, <filename, arguments, values>);
        end if;
    end for;
    return res;
end intrinsic;

intrinsic WriteStderr(s::MonStgElt)
{ write to stderr }
  E := Open("/dev/stderr", "a");
  Write(E, s);
  Flush(E);
end intrinsic;

intrinsic WriteStderr(e::Err)
{ write to stderr }
  WriteStderr(Sprint(e) cat "\n");
end intrinsic;

intrinsic Coefficients(C::CrvHyp) -> SeqEnum
{ Returns [Coefficients(f),Coefficients(h)] for the hyperelliptic curve y^+h(x)y = f(x). }
    return [Coefficients(f),Coefficients(h)] where f,h := HyperellipticPolynomials(C);
end intrinsic;

intrinsic Coefficients(C::CrvPln) -> SeqEnum
{ Returns dense list of coefficients of the defining polynomial of C (in lex order matching MonomialsOfDegree). }
    f := DefiningPolynomial(C); d := Degree(f);
    c := Coefficients(f); m := Monomials(f);
    M := MonomialsOfDegree(Parent(f),Degree(f));
    r := [0:i in [1..#M]]; for i:=1 to #c do r[Index(M,m[i])] := c[i]; end for;
    return r;
end intrinsic;

intrinsic CoefficientString(C::Crv) -> SeqEnum
{ Returns a string encoding the cofficients of the curve C. }
    return sprint(Coefficients(C));
end intrinsic;

intrinsic facpat(f::RngUPolElt:SquareFree:=false) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) (specificed by its coefficients). }
    if IsFinite(BaseRing(f)) then
        return Degree(f) le 0 select {**} else (SquareFree select {* a[1]^^(Degree(a[2]) div a[1]) : a in DistinctDegreeFactorization(f) *}
                                          else &join[{* a[1]^^(Degree(a[2]) div a[1]) : a in DistinctDegreeFactorization(b[1]) *}: b in SquarefreeFactorization(f)]);
    else
        return Degree(f) le 0 select {**} else {* Degree(a[1])^^a[2] : a in Factorization(f) *};
    end if;
end intrinsic;

intrinsic facpat(f::SeqEnum[RngIntElt]:SquareFree:=false) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) (specificed by its coefficients). }
    return facpat(PolynomialRing(Integers())!f:SquareFree:=SquareFree);
end intrinsic;

intrinsic facpat(f::RngUPolElt, p::RngIntElt:SquareFree:=false) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) modulo p (specificed by its coefficients). }
    return facpat(ChangeRing(f,GF(p)):SquareFree:=SquareFree);
end intrinsic;

intrinsic facpat(f::SeqEnum[RngIntElt], p::RngIntElt:SquareFree:=false) -> SetMulti[RngIntElt]
{ Returns the factorization pattern of the univariate polynomial f(x) (specificed by its coefficients). }
    return facpat(PolynomialRing(GF(p))!f:SquareFree:=SquareFree);
end intrinsic;

intrinsic EasyFactorization(n::RngIntElt:TrialDivisionLimit:=2^20,ECMLimit:=1000,PrimeLimit:=200,mLimit:=40,nECMLimit:=800,nLimit:=4000) -> RngIntEltFact, RngIntElt
{ Attempts to factor the specified nonzero integer n using a bounded amount of effort by setting ECMLimit to a fixed value (default is 1000) and MPQSLimit:=0, and bounding the size of primes allowed in the factorization (default is 100 decimal digits) and the size of the input integer n (default is 1000 decimal digits).
  If succesful the full (provably correct) factorization is returned, followed by the sign; otherwise a (provably correct) partial factorization and zero are returned. }
    if Abs(n) le 10^mLimit then return Factorization(n), Sign(n); end if;
    if Abs(n) eq 1 then return [], n; end if;
    require Abs(n) gt 1: "Input must be nonzero";
    d := Log(10,Abs(n));
    if d gt nLimit then return [],0; end if;
    P,s,E := Factorization(n:TrialDivisionLimit:=TrialDivisionLimit,ECMLimit:=d gt nECMLimit select 0 else ECMLimit,MPQSLimit:=0,Proof:=false);
    if assigned E then
        if Max([Log(10,Abs(e)):e in E]) gt nECMLimit then return P,0; end if;
        E := &cat[n eq 0 select [e] else [n,e div n] where n:=ECMSteps(e,250,1000):e in E];
        if #E eq 1 then
            if E[1] le 10^mLimit then P cat:= Factorization(E[1]); else s:=0; end if;
        else
            Q := CoprimeBasis(E);
            for q in Q do
                PP,ss,EE := Factorization(q[1]:TrialDivisionLimit:=TrialDivisionLimit,ECMLimit:=ECMLimit,MPQSLimit:=0,Proof:=false);
                if assigned EE then s:=0; end if;
                P cat:= [<p[1],p[2]*q[2]>:p in PP];
            end for;
        end if;
        P := Eltseq({*p[1]^^p[2]:p in P*});
    end if;
    pmax := 10^PrimeLimit;
    for i:=1 to #P do if P[i][1] gt pmax or not IsPrime(P[i][1]) then return P[1..i-1],0; end if; end for;
    return P,s;
end intrinsic;

intrinsic PrimeDivisors(S::SeqEnum[RngIntElt] : AllowComposites:=false) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt]
{ Given a sequence of integers S, returns a sequence primes optionally followed by a sequence of composites,
  such that the elements in the two lists together form a factor basis for S: every element in the lists divides an element of s, no two have a common factor,
  and every element of s is a product of powers of elements in these lists.  When composites are allowed EasyFactorization will be used to avoid expensive factorizations. }
    S := CoprimeBasis([Abs(n):n in S|Abs(n) gt 1]);
    S := [s[1]:s in S];
    if not AllowComposites then return Sort(&cat[PrimeDivisors(n):n in S]), true; end if;
    P := []; sts := true;
    for n in S do
        i:=#P+1;
        Q,s := EasyFactorization(n);
        P cat:= [q[1]:q in Q];
        if s eq 0 then
            P cat:= [n div &*[Integers()|q[1]^q[2]:q in Q]];
            sts := false;
        end if;
    end for;
    return Sort(P), sts;
end intrinsic;

intrinsic Valuation(r::FldRatElt,p::RngIntElt,isprime::BoolElt) -> RngIntElt
{ Given a rational number r and a positive integer p returns the least integer n such the denominator of r/p^n is coprime to p.
  When isprime is true this function computes the p-adic valuation using Valuation(r,p). }
    if r eq 0 or isprime then return Valuation(r,p); end if;
    n := 0;
    while IsDivisibleBy(Numerator(r),p^(n+1)) do n+:=1; end while;
    if n gt 0 then return n; end if;
    while GCD(Denominator(r*p^n),p) ne 1 do n+:=1; end while;
    return -n;
end intrinsic;

intrinsic NormalizedProjectiveInvariants (v::SeqEnum[FldRatElt], w::SeqEnum[RngIntElt] : Easy:=false) -> SeqEnum, FldRatElt, BoolElt
{ Given a list of rational numbers v and a corresponding positive integer weights w, returns a list of integers z and a nonzero rational number r such that z[i] = v[i]*r^w[i] for all i.
  The Easy parameter can be used to avoid hard-to-factor integers.
  The third return value indicates whether the returned vector z is gauranteed to be minimal (it may be false if Easy is set). }
    require #v eq #w: "The sequences v and w  must have the same length.";
    require &or[c ne 0:c in v]: "At least one entry of v must be nonzero.";
    require &and[c gt 0: c in w]: "The weights must be positive.";
    P,b := PrimeDivisors(&cat[[Numerator(c),Denominator(c)]:c in v]:AllowComposites:=Easy);
    r := &*[Rationals()|p^Min([Floor(Valuation(v[i],p,b)/w[i]):i in [1..#v]|v[i] ne 0]):p in P];
    z := [Integers()|v[i]*r^(-w[i]):i in [1..#v]];
    O := [i:i in [1..#z]|z[i] ne 0 and IsOdd(w[i])];
    if #O gt 0 and v[O[1]] lt 0 then z := [Integers()|(-1)^w[i]*z[i]:i in [1..#z]]; r := -r; end if;
    return z,r,b;
end intrinsic;

intrinsic NormalizedIgusaClebschInvariants (C::CrvHyp : Easy:=false) -> SeqEnum
{ Normalized Igusa-Clebsch invariants of genus 2 hyperelliptic curve (the invariants must lie in Q or Fp, but the curve need not be defined over Q or Fp). }
    inv := IgusaClebschInvariants(C); F := BaseRing(C);
    if IsFinite(F) and IsPrime(#F) then
        if #F eq 2 then return inv; end if;
        p := #F;
        ZZ := Integers(); R<t> := PolynomialRing(F);
        if inv[1] ne 0 then
            return [1,c^2*inv[2],c^3*inv[3],c^5*inv[5]] where c := 1/inv[1];
        elif inv[2] ne 0 then
            r := PowerClassRepresentative(inv[2],2); c := Roots(t^2-r/inv[2])[1][1];
            inv1 := [0,r,c^3*inv[3],c^5*inv[5]]; c:=-c;
            inv2 := [0,r,c^3*inv[3],c^5*inv[5]];
            return i where i:=Min([inv1,inv2]);
        elif inv[3] ne 0 then
            r := PowerClassRepresentative(inv[3],3); c := Roots(t^3-r/inv[3])[1][1];
            inv1 := [0,0,r,c^4*inv[4],c^5*inv[5]];
            if p mod 3 ne 1 then return inv; end if;
            z := (R!PrimitiveRoot(p))^((p-1) div 3);
            c *:= z; inv2 := [0,0,r,c^5*inv[5]];
            c *:= z; inv3 := [0,0,r,c^5*inv[5]];
            return a where a:=Min([inv1,inv2,inv3]);
        else
            return [0,0,0,0,PowerClassRepresentative(inv[5],5)];
        end if;
    end if;
    require &and[c in Rationals():c in inv]: "The Igusa-Clebsch invariants must lie in Q or Fp.";
    return z where z:=NormalizedProjectiveInvariants([Rationals()!c:c in inv], [1,2,3,5] : Easy:=Easy);
end intrinsic;

intrinsic NormalizedIgusaInvariants (C::CrvHyp : Easy:=false) -> SeqEnum
{ Normalized Igusa invariants of genus 2 hyperelliptic curve (the invariants must lie in Q, but the curve need not be defined over Q).
  The optional parameter Bound can be used to restrict the primes that can be used in the normalization when the invariants lie in Q. }
    inv := IgusaInvariants(C); F := BaseRing(C);
    if IsFinite(F) and IsPrime(#F) then
        if #F eq 2 then return inv; end if;
        p := #F;
        ZZ := Integers(); R<t> := PolynomialRing(F);
        if inv[1] ne 0 then
            return [1,c^2*inv[2],c^3*inv[3],c^4*inv[4],c^5*inv[5]] where c := 1/inv[1];
        elif inv[2] ne 0 then
            r := PowerClassRepresentative(inv[2],2); c := Roots(t^2-r/inv[2])[1][1];
            inv1 := [0,r,c^3*inv[3],c^4*inv[4],c^5*inv[5]]; c:=-c;
            inv2 := [0,r,c^3*inv[3],c^4*inv[4],c^5*inv[5]];
            return i where i:=Min([inv1,inv2]);
        elif inv[3] ne 0 then
            r := PowerClassRepresentative(inv[3],3); c := Roots(t^3-r/inv[3])[1][1];
            inv1 := [0,0,r,c^4*inv[4],c^5*inv[5]];
            if p mod 3 ne 1 then return inv1; end if;
            z := (R!PrimitiveRoot(p))^((p-1) div 3);
            c *:= z; inv2 := [0,0,r,c^4*inv[4],c^5*inv[5]];
            c *:= z; inv3 := [0,0,r,c^4*inv[4],c^5*inv[5]];
            return a where a:=Min([inv1,inv2,inv3]);
        elif inv[4] ne 0 then
            r := PowerClassRepresentative(inv[4],4); c := Roots(t^4-r/inv[4])[1][1];
            inv1 := [0,0,0,r,c^5*inv[5]];
            c := -c; inv2 := [0,0,0,r,c^5*inv[5]];
            if p mod 4 ne 1 then
                return i where i:=Min([inv1,inv2]);
            else
                z := (R!PrimitiveRoot(p))^((p-1) div 4);
                c *:= z; inv3 := [0,0,0,r,c^5*inv[5]];
                c := -c; inv4 := [0,0,0,r,c^5*inv[5]];
                return i where i:=Min([inv1,inv2,inv3,inv4]);
            end if;
        else
            return [0,0,0,0,PowerClassRepresentative(inv[5],5)];
        end if;
    end if;
    require &and[c in Rationals():c in inv]: "The Igusa-Clebsch invariants must lie in Q or Fp.";
    return z where z:=NormalizedProjectiveInvariants([Rationals()!c:c in inv], [1,2,3,4,5] : Easy:=Easy);
end intrinsic;

intrinsic NormalizedModularIgusaInvariants (C::CrvHyp : Easy:=false) -> SeqEnum
{ Returns the "modular invariants" of the genus 2 curve C as defined in arXiv:2301.10118.
    The optional parameter Bound can be used to restrict the primes that can be used in the normalization when the invariants lie in Q. }
    I := IgusaClebschInvariants(C);
    require &and[c in Rationals():c in I]: "The Igusa-Clebsch invariants must lie in Q.";
    J := [I[2]/4,(I[1]*I[2]-3*I[3])/8,-I[4]/4096,I[1]*I[4]/2^15];
    return z where z:=NormalizedProjectiveInvariants(J, [2,3,5,6] : Easy:=Easy);
end intrinsic;

intrinsic NormalizedShiodaInvariants (C::CrvHyp : Easy:=false) -> SeqEnum
{ Normalized Shioda invariants of genus 3 hyperelliptic curve (the invariants must lie in Q, but the curve need not be defined over Q). }
    require Genus(C) eq 3: "Genus 3 curve required.";
    inv, w := ShiodaInvariants(C);
    inv := WPSNormalize(w,inv);
    require &and[c in Rationals():c in inv]: "The Shioda invariants must lie in Q.";
    return z where z:=NormalizedProjectiveInvariants([Rationals()!c:c in inv],w : Easy:=Easy);
end intrinsic;

intrinsic NormalizedShiodaInvariants (f::RngUPolElt,h::RngUPolElt : Easy:=false) -> SeqEnum
{ Normalized Shioda invariants of genus 3 hyperelliptic curve (the invariants must lie in Q, but the curve need not be defined over Q). }
    C := HyperellipticCurve(f,h);
    return NormalizedShiodaInvariants(C : Easy:=Easy);
end intrinsic;

intrinsic NormalizedDixmierOhnoInvariants (f::RngMPolElt : Easy:=false) -> SeqEnum
{ Normalized Dixmier-Ohno invaraints of smooth plane quartic f(x,y,z)=0 defined over Q. }
    require VariableWeights(Parent(f)) eq [1,1,1] and IsHomogeneous(f) and Degree(f) eq 4: "Input muste be a ternary quartic form.";
    R := BaseRing(Parent(f));
    require Type(R) eq FldRat or Type(R) eq RngInt: "Curve must be defined over Q.";
    inv, w := DixmierOhnoInvariants(f:normalize);
    return z where z:=NormalizedProjectiveInvariants(inv,w: Easy:=Easy);
end intrinsic;

intrinsic NormalizedDixmierOhnoInvariants (C::CrvPln : Easy:=false) -> SeqEnum
{ Normalized Dixmier-Ohno invaraints of smooth plane quartic C:f(x,y,z)=0 defined over Q. }
    return NormalizedDixmierOhnoInvariants(DefiningPolynomial(C) : Easy:=Easy);
end intrinsic;
intrinsic SPQInvariants (f::RngMPolElt : Easy:=false) -> SeqEnum
{ Normalized Dixmier-Ohno invaraints of smooth plane quartic f(x,y,z)=0 defined over Q. }
    return NormalizedDixmierOhnoInvariants(f : Easy:=Easy);
end intrinsic;

intrinsic SPQInvariants (f::MonStgElt : Easy:=false) -> SeqEnum
{ Normalized Dixmier-Ohno invaraints of smooth plane quartic f(x,y,z)=0 defined over Q. }
  R<x,y,z>:=PolynomialRing(Rationals(),3);
  return SPQInvariants(eval(f) : Easy:=Easy);
end intrinsic;

intrinsic SPQIsIsomorphic(f1::RngMPolElt, f2::RngMPolElt) -> BoolElt, GrpMatElt
{ Tests isomorphism of smooth plane curves f(x,y,z)=0 by computing a matrix M in GL(3,F) such that f1^M is a scalar multiple of f2. Original implementation due to Michael Stoll.}
    require VariableWeights(Parent(f1)) eq [1,1,1] and IsHomogeneous(f1) and Degree(f1) eq 4 and
            VariableWeights(Parent(f2)) eq [1,1,1] and IsHomogeneous(f2) and Degree(f2) eq 4: "Inputs must be ternary quartic forms.";
    R := Parent(f1);
    if not IsField(BaseRing(R)) then R:=PolynomialRing(FieldOfFractions(BaseRing(R)),3); f1:=R!f1; f2:=R!f2; end if;
    f2 := R!f2; // make sure both f1 and f2 live in the same structure
    F := BaseRing(R);
    /*
     We need to determine whether there exists an invertible matrix M such that f1^M is a scalar multiple of f2.
     The matrix is determined only up to scaling; to reduce to a finite set, we set one of the entries equal to 1.
     This leads to three different cases, depending on which entry in the first row of M is the first nonzero entry.
    */

    // We begin with the most overdetermined case, with first row (0 0 1).
    A<[a]> := AffineSpace(F, 7);
    mat := Matrix(CoordinateRing(A), 3,3, [0,0,1] cat a[1..6]);
    PA := PolynomialRing(CoordinateRing(A), 3);
    fPA := PA!f1;
    f1PA := PA!f2;
    f2PA := fPA^mat;
    mons := MonomialsOfDegree(PA, 4);
    tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                     [MonomialCoefficient(f2PA, m) : m in mons]]);
    S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[7]-1]);
    pts := Points(S);
    if not IsEmpty(pts) then
        M := GL(3,F)!Matrix(F, 3,3, [0,0,1] cat Eltseq(pts[1])[1..6]);
    else
        // Now we look at first row (0 1 *).
        A<[a]> := AffineSpace(F, 8);
        mat := Matrix(CoordinateRing(A), 3,3, [0,1] cat a[1..7]);
        PA := PolynomialRing(CoordinateRing(A), 3);
        fPA := PA!f1;
        f1PA := PA!f2;
        f2PA := fPA^mat;
        mons := MonomialsOfDegree(PA, 4);
        tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                           [MonomialCoefficient(f2PA, m) : m in mons]]);
        S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[8]-1]);
        pts := Points(S);
        if not IsEmpty(pts) then
            M := GL(3,F)!Matrix(F, 3,3, [0,1] cat Eltseq(pts[1])[1..7]);
        else
            // Finally, the generic case, first row is (1 * *)
            A<[a]> := AffineSpace(F, 9);
            mat := Matrix(CoordinateRing(A), 3,3, [1] cat a[1..8]);
            PA := PolynomialRing(CoordinateRing(A), 3);
            fPA := PA!f1;
            f1PA := PA!f2;
            f2PA := fPA^mat;
            mons := MonomialsOfDegree(PA, 4);
            tworows := Matrix([[MonomialCoefficient(f1PA, m) : m in mons],
                             [MonomialCoefficient(f2PA, m) : m in mons]]);
            S := Scheme(A, Minors(tworows, 2) cat [Determinant(mat)*a[9]-1]);
            pts := Points(S);
            if IsEmpty(pts) then return false,_; end if;
            M := GL(3,F)!Matrix(F, 3,3, [1] cat Eltseq(pts[1])[1..8]);
        end if;
    end if;
    f := f1^M;
    assert LeadingCoefficient(f2)*f eq LeadingCoefficient(f)*f2;
    return true, M;
end intrinsic;

intrinsic GeometricAutomorphismField(C::CrvHyp) -> Fld
{ Returns the minimal field over which the all automorphisms of the hyperelliptic curve C are defined. }
    A := AutomorphismsOfHyperellipticCurve(C:geometric,commonfield:=false);
    nf := func<K|Degree(K) eq 1 select RationalsAsNumberField() else NormalClosure(AbsoluteField(K))>;
    K := nf(BaseRing(A[1][1]));
    for i:=2 to #A do
        L:=nf(BaseRing(A[i][1]));
        K:=Compositum(K,L);
    end for;
    return K;
end intrinsic;

intrinsic MonicQuadraticRoots(b::RngIntElt, c::RngIntElt, p::RngIntElt, e:RngIntElt) -> SeqEnum[RngIntElt]
{ Returns the complete list of solutions to x^2+bx+c = 0 in Z/p^eZ for p prime and e ge 1 (does not verify the primality of p). }
    require e gt 0: "e must be positive";
    q := p^e;
    b mod:= q; c mod:= q;
    // for the sake of simplicity we just hensel linearly; this could/should be improved
    if p eq 2 then
        if IsOdd(c) and IsOdd(b) then return [Integers()|]; end if;
        S := IsEven(c) select (IsOdd(b) select [0,1] else [0]) else [1];
    else
        bp := GF(p)!b;
        s,u := IsSquare(bp^2-4*c);
        if not s then return [Integers()|]; end if;
        S := u eq 0 select [Integers()|-bp/2] else [Integers()|(-bp-u)/2,(-bp+u)/2]; // solutions mod p
    end if;
    m := p;
    lift := func<x,p,m|x+m*Integers()!(-1/(GF(p)!2*x+b)*((x*(x+b)+c) div m))>;
    for n:=2 to e do
        mm := m*p;
        S := &cat[(2*x+b) mod p eq 0 select ((x*(x+b)+c) mod mm eq 0 select [x+m*i:i in [0..p-1]] else [Integers()|]) else [lift(x,p,m)] : x in S];
        if #S eq 0 then return S; end if;
        m := mm;
    end for;
    return S;
end intrinsic;

intrinsic MonicQuadraticRoots(b::RngIntElt, c::RngIntElt, m::RngIntElt) -> SeqEnum[RngIntElt]
{ Returns the complete list of solutions to x^2+bx+c = 0 in Z/mZ. }
    require m ge 2: "m must be at least 2";
    M := Factorization(m);
    return [CRT([v[i]:i in [1..#M]],[a[1]^a[2]:a in M]) : v in CartesianProduct([MonicQuadraticRoots(b,c,a[1],a[2]):a in M])];
end intrinsic;

intrinsic ChangeRing(f::RngUPolElt, pi::Map) -> RngUPolElt
{ Given f = sum a_i*x^i returns sum pi(a_i)*x^i }
    return PolynomialRing(Codomain(pi))![pi(c):c in Coefficients(f)];
end intrinsic;

intrinsic PrimePowers(B::RngIntElt) -> SeqEnum[RngInt]
{ Ordered list of prime powers q <= B (complexity is O(B log(B) loglog(B)), which is suboptimal but much better than testing individual prime powers). }
    if B lt 2 then return [Integers()|]; end if;
    P := PrimesInInterval(2,B); L := Floor(Log(2,B));
    I := [#P] cat [Index(P,NextPrime(Floor(B^(1/n))))-1:n in [2..L]];
    // sorting is asymptotically stupid (we could merge in linear time or just sieve), but this is not the dominant step for the B we care about
    // even at 10^9 more than half the time is spent enumerating primes
    return Sort(&cat[[p^n:p in P[1..I[n]]]:n in [1..L]]);
end intrinsic;

intrinsic ProperDivisors(N::RngIntElt) -> SeqEnum[RngIntElt]
{ Sorted list of postive proper divisors of the integer N. }
    return N eq 1 select [] else D[2..#D-1] where D:=Divisors(N);
end intrinsic;

intrinsic PrimesInInterval(K::FldNum,min::RngIntElt,max::RngIntElt:coprime_to:=1) -> SeqEnum
{ Primes of K with norm in [min,max]. }
    S := PrimesUpTo(max,K:coprime_to:=coprime_to); 
    return max lt 2 select S else [p:p in S|Norm(p) ge min];
end intrinsic;

// This is often slower than &+[r[2]:r in Roots(f)] but faster when f has lots of roots, e.g. splits completely
intrinsic NumberOfRoots(f::RngUPolElt[FldFin]) -> RngIntElt
{ The number of rational roots of the polynomial f. }
    a := SquareFreeFactorization(f);
    b := [DistinctDegreeFactorization(r[1]:Degree:=1):r in a];
    return &+[Integers()|a[i][2]*(#b[i] gt 0 select Degree(b[i][1][2]) else 0):i in [1..#a]];
end intrinsic;

intrinsic TracesToLPolynomial (t::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of Frobenius traces of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    require IsPrimePower(q): "q must be a prime power.";
    R<T> := PolynomialRing(Integers());
    if #t eq 0 then return R!1; end if;
    g := #t;
    // use Newton identities to compute compute elementary symmetric functions from power sums
    e := [t[1]];  for k:=2 to g do e[k] := ExactQuotient((-1)^(k-1)*t[k]+&+[(-1)^(i-1)*e[k-i]*t[i]:i in [1..k-1]],k); end for;
    return R!([1] cat [(-1)^i*e[i]:i in [1..g]] cat [(-1)^(g-i)*q^i*e[g-i]:i in [1..g-1]] cat [q^g]);
end intrinsic;

intrinsic PointCountsToLPolynomial (n::SeqEnum[RngIntElt], q::RngIntElt) -> RngUPolElt
{ Given a sequence of point counts of a genus g curve over Fq,Fq^2,...,Fq^g returns the corresponding L-polynomial. }
    return TracesToLPolynomial([q^i+1-n[i] : i in [1..#n]], q);
end intrinsic;

intrinsic LPolynomialToTraces (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of Frobenius traces for a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    require Degree(L) gt 0 and IsEven(Degree(L)): "Lpolynomial must have positive even degree 2g";
    g := ExactQuotient(Degree(L),2);
    b,p,e := IsPrimePower(Integers()!LeadingCoefficient(L));
    require b: "Not a valid L-polynomial, leading coefficient is not a prime power";
    require IsDivisibleBy(e,g): "Not a valid L-polynomial, leading coefficient is not a prime power with an integral gth root.";
    q := p^ExactQuotient(e,g);
    L := Reverse(L);
    if d eq 0 then d:=g; end if;
    e := [Integers()|(-1)^i*Coefficient(L,2*g-i):i in [1..d]];
    // use Newton identities to compute compute power sums from elementary symmetric functions;
    t := [e[1]]; for k:=2 to d do t[k] := (-1)^(k-1)*k*e[k] + &+[(-1)^(k-1+i)*e[k-i]*t[i] : i in [1..k-1]]; end for;
    return t, q;
end intrinsic;

intrinsic LPolynomialToPointCounts (L::RngUPolElt:d:=0) -> SeqEnum[RngIntElt], RngIntElt
{ Returns the sequence of point counrs of a genus g curve over Fq,Fq^2,...,Fq^g corresponding to the givien L-polynomial of degree 2g (or just over Fq,..Fq^d if d is specified). }
    t, q := LPolynomialToTraces(L:d:=d);
    if d eq 0 then d := #t; end if;
    return [q^i+1-t[i] : i in [1..d]];
end intrinsic;

intrinsic ParallelJobs (cmd::MonStgElt, jobs::RngIntElt, workers::RngIntElt:infile:="",vkey:="")
{ Runs the specified cmd (which may contain multiple ;-terminated Magma commands) in parallel across the specified number of jobs using the specified number of workers (each as a separate process), using GNU parallel if the number of workers is greater than 1.
  The string jobid will be set to 0,1,...,jobs-1 in each job; cmd can use this to distinguish the job it is running.
  The optional string infile can used to specify that job n is to be run only when infile_n is nonempty.
  The optional string vkey can be used to propagate a verbosity setting into workers. }
    require workers gt 0: "number of workers must be positive";
    if jobs le 0 then printf "ParallelJobs called with no jobs, nothing to do!"; return; end if;
    gotwork := infile eq "" select func<i|true> else func<i|not IsEof(Read(Open(infile cat "_" cat itoa(i),"r"),1))>;
    if workers gt jobs then workers := jobs; end if;
    if workers eq 1 then
        vprintf ParallelJobs: "ParallelJobs running %o jobs inline: %o\n", jobs, cmd;
        cnt := 0; for i:=0 to jobs-1 do if gotwork(i) then jobid:=itoa(i); sts := eval cmd cat "; return true;"; cnt +:= 1; end if; end for;
        return;
    end if;
    jobfile := Tempname("magmajob"); jobsfile := Tempname("magmajobs"); logfile := Tempname("magmajoblog"); Flush(Open(logfile,"w"));
    if #vkey gt 0 then
        Puts(Open(jobfile,"w"),
             Sprintf("SetVerbose(\"%o\",%o); try %o; catch e print e`Object; print e`Position; print \"segfaulting to force retry\"; func<n|$$(n+1)>(1); end try; fp:=Open(\"%o_done_\" cat jobid,\"w\"); Puts(Open(\"%o_\" cat jobid,\"a\"),jobid); exit;",
                     vkey,GetVerbose(vkey), cmd, jobfile, logfile));
    else
        Puts(Open(jobfile,"w"),
             Sprintf("try %o; catch e print e`Object; print e`Position; print \"segfaulting to force retry\"; func<n|$$(n+1)>(1); end try; fp:=Open(\"%o_done_\" cat jobid,\"w\"); Puts(Open(\"%o_\" cat jobid,\"a\"),jobid); exit;",
                     cmd, jobfile, logfile));
    end if;
    fp := Open(jobsfile,"w"); joblist := [];
    for i:=0 to jobs-1 do if gotwork(i) then donefile := jobfile cat "_done_" cat itoa(i); Puts(fp, Sprintf("rm -f %o ; until [ -f \"%o\" ]; do magma -b jobid:=%o %o ; if ! [ -f %o ]; then echo \"retrying job %o\"; fi; done; rm -f %o ;", donefile, donefile, i, jobfile, donefile, i, donefile)); Append(~joblist,i); end if; end for;
    delete fp;
    if workers gt #joblist then workers := #joblist; end if;
    if #joblist gt workers then vprintf ParallelJobs: "RunJobs using parallel to split %o tasks across %o threads\n", #joblist, workers; end if;
    timer := Realtime();
    System(Sprintf("rm -f %o_* ; parallel -u --joblog /tmp/log --jobs %o -u < %o ; cat %o_* > %o 2>/dev/null ; rm -f %o_*", logfile, workers, jobsfile, logfile, logfile, logfile));
    okay := {atoi(r):r in Split(Read(logfile))};
    missing := [i:i in joblist|not i in okay];
    if #missing gt 0 then print "FAILURE: error in ParallelJobs, parallel missed jobs:", sprint(missing); error "Jobs retry failed"; end if;
    System(Sprintf("rm %o %o %o",jobfile,jobsfile,logfile));
    vprintf ParallelJobs: "ParallelJobs parallel execution of %o jobs using %o workers%o took %.3os (\"%o\")\n", #joblist, workers, okay eq Set(joblist) select "" else " failed and", Realtime()-timer, cmd;
end intrinsic

intrinsic PrimeCount (n::RngIntElt) -> RngIntElt
{ Returns pi(n) (using primecount). }
    return atoi(Pipe("primecount " cat itoa(n),""));
end intrinsic;

intrinsic PrimeCount (m::RngIntElt,n::RngIntElt) -> RngIntElt
{ Returns pi(n)-pi(m-1) (using primecount). }
    return n ge m select PrimeCount(n)-PrimeCount(m-1) else 0;
end intrinsic;

intrinsic SmoothNumberCount (P::SeqEnum[RngIntElt], B::RngIntElt) -> RngIntElt
{ Counts the positive integers <= B whose prime factors lie in P. The primality of the integers in P is not verified.  }
    require B gt 0: "B must be positive";
    S := []; for p in P do Append(~S,p); q := p*p; while q lt B do Append(~S,q); q *:= q; end while; end for;
    S := Sort(S);
    T:=[1]; cnt := 0;
    for s in S do
        Q:=[]; Tmax := B div s; Qmax := Tmax div s;
        Q := [n:n in T|n le Tmax]; cnt +:= #T-#Q; assert #T-#Q eq #(Set(T) diff Set(Q));
        T := [n*s:n in Q|n le Qmax]; cnt +:= #Q-#T; assert #Q-#T eq #(Set([n*s:n in Q]) diff Set(T));
        T cat:= Q;
    end for;
    return cnt + #T;
end intrinsic;

intrinsic SmoothNumbers (P::SeqEnum[RngIntElt], B::RngIntElt: B0:=1) -> SeqEnum[RngIntElt]
{ Returns a list of the integers in [B0,B] whose prime factors lie in P (B0=1 if unspecified). The primality of the integers in P is not verified.  }
    require B0 gt 0 and B ge B0: "B0 <= B must be positive";
    S := []; for p in P do Append(~S,p); q := p*p; while q lt B do Append(~S,q); q *:= q; end while; end for;
    S := Sort(S);
    T:=[1]; L := [];
    for s in S do
        Q:=[]; Tmax := B div s; Qmax := Tmax div s;
        Q := [n:n in T|n le Tmax];
        L cat:= [n:n in T|n ge X] where X:=Max(B0,Tmax+1);
        T := [n*s:n in Q|n le Qmax];
        L cat:= [n*s:n in Q|n ge X] where X:=Max((B0+s-1) div s,Qmax+1);
        T cat:= Q;
    end for;
    L cat:= [n:n in T|n ge B0]; L := Sort(L);
    return L;
end intrinsic;

intrinsic PowerClassRepresentative (a::RngIntElt, p::RngIntElt, n::RngIntElt:Root:=false) -> RngIntElt
{ Returns the least nonnegative integer b for which a*c^n = b for some c in Fp (intended for small n, this will be very slow if gcd(n,p-1) is large). }
    require IsProbablePrime(p): "p must be prime";
    require n gt 0: "n most be positive";
    a := a mod p; if a le 1 then return a; end if;
    n := GCD(p-1,n);
    if n eq 1 then return 1; end if;
    e := (p-1) div n;
    ai := GF(p)!1/a;
    for b:=1 to p-1 do if (b*ai)^e eq 1 then return b; end if; end for;
    error Sprintf("No power class representative found for a=%o, p=%o, n=%o\n",a,p,n);
end intrinsic;

intrinsic PowerClassRepresentative (a::FldFinElt, n::RngIntElt) -> RngIntElt
{ Returns the least nonnegative integer b for which a = b*c^n for some c in Fp (intended for small n, this will be very slow if gcd(n,p-1) is large). }
    p := #Parent(a);
    require IsProbablePrime(p): "finite field must have prime order";
    return PowerClassRepresentative(Integers()!a,p,n);
end intrinsic;

intrinsic SquareFree (f::RngUPolElt) -> RngUPolElt, RngUPolElt
{ Given a univariate polynomial over a field whose characteristic is 0 or exceeds the degree of f, returns polynomials g,h with h monic such that f = g*h^2. }
    p := Characteristic(BaseRing(f));
    require p eq 0 or p gt Degree(f): "The input polynomial f must be defined over a field of characterstic p with p=0 or p > deg(f).";
    // Run a simplified version of Yun's algorithm
    c := LeadingCoefficient(f); f div:= c;
    d := GCD(f,Derivative(f));
    w := f div d;
    i := 1;
    h := 1;
    while w ne 1 do
        y := GCD(w,d);
        a,w,d := w div y, y, d div y;
        h *:= a^Floor(i/2);
        i +:= 1;
    end while;
    return c*(f div h^2), h;
end intrinsic;

// ComplexExtra and RationalsExtra copied from endomorphisms relative.m to remove dependency
declare attributes FldCom : epscomp, epsinv, height_bound, prec_algdep;
declare attributes FldRe  : epscomp, epsinv, height_bound, prec_algdep;
declare attributes FldNum : base, base_gen, CC, iota, aut;
declare attributes FldRat : base, base_gen, CC, iota, aut;

intrinsic ComplexFieldExtra(prec::RngIntElt) -> FldCom
{ Returns a complex field of the given precision with the extra attributes epscomp, epsLLL, epsinv and height_bound. }
    CC := ComplexField(prec);
    RR := RealField(CC);
    if prec lt 200 then
        CC`epscomp := RR ! (10^(-prec + 10)); CC`epsinv  := RR ! 10^(-6); CC`height_bound := 10^6; CC`prec_algdep := prec - 5;
        RR`epscomp := CC`epscomp; RR`epsinv := CC`epsinv; RR`height_bound := CC`height_bound; RR`prec_algdep := CC`prec_algdep;
        return CC;
    end if;
    CC`epscomp := RR ! (10^(-Round(9.5*prec/10))); CC`epsinv  := RR ! (2^(-prec)); CC`height_bound := RR ! (3^(30 + (prec div 10))); CC`prec_algdep := Round(8*prec/10);
    RR`epscomp := CC`epscomp; RR`epsinv := CC`epsinv; RR`height_bound := CC`height_bound; RR`prec_algdep := CC`prec_algdep;
    return CC;
end intrinsic;

intrinsic ComplexFieldExtra() -> FldCom
{ Default ComplexFieldExtra with precision 100. }
    return ComplexFieldExtra(100);
end intrinsic;

intrinsic InfinitePlacesExtra(K::Fld) -> SeqEnum
{ The infinite places of K, represented by the roots of the generator in the associated complex field. No identification of complex conjugate places takes place. }
    return [ tup[1] : tup in Roots(MinimalPolynomial(K.1), ComplexFieldExtra(Precision(K`CC) + 10)) ];
end intrinsic;

intrinsic RationalsExtra(prec::RngIntElt) -> FldNum
{ Returns the rationals with itself as base and an infinite place with the given precision. }
    K := Rationals();
    K`base := K; K`base_gen := K ! 1; K`CC := ComplexFieldExtra(prec); K`iota := InfinitePlacesExtra(K)[1];
    return K;
end intrinsic;

intrinsic RationalsExtra() -> FldNum
{ Default RationalsExtra with precision 100. }
    return RationalsExtra(100);
end intrinsic;
