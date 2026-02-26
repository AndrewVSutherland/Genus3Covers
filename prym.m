// We assume https://github.com/AndrewVSutherland/Magma/blob/main/utils.m is already attached (e.g. in your magma startup file)
// If that is not the case, download it and insert 'Attach("utils.m");' before the line below attaching g3cover.m.
Attach("g3cover.m"); // depends on utils.m

if not assigned P and not assigned Kstr then
	print "usage: magma -b arg:=val ... prym.m\n";
    print "Supported values of arg include:\n";
    print "  P (val is a bad prime bound or list of bad primes allowed; this is required unless Estr and Kstr are both specified)";
    print "  pnum (val is a positive integer bound on the number of odd bad primes allowed; default is 5)";
    print "  radminp (val is a positive integer (strict) lower bound on the primes to ignore when applying radmax; default is 1)";
    print "  radmax (val is a positive integer bounding the product of primes > radminp; default is 2^19)";
    print "  Nmax (val is a positive integer bound on the conductor of elliptic curves to consider; default is 1000)";
    print "  Dmax (val is a positive integer bound on the absolute value of the discriminant of number fields to consider; default is 10000)";
    print "  Efile (val is the name of a file of elliptic curves E to use, with rows N:[a1,a2,a3,a4,a6], where N is the conductor of E;";
    print "         default is to use all E/Q of conductor <= min(Nmax,500000) (the Cremona DB is included in Magma)";
    print "  Kfile (val is the name of a file of number fields K to use, with rows D:[f0,f1,...fd], where D=|disc(K)| and K=Q[x]/(f0+f1*x+...+fd*x^d);";
    print "         default is to use number fields listed in the file lmfdb_prym_nf.txt, which includes Q and all number fields satsfying";
    print "         d=2 and either D <= 2000000 or D 17-smooth";
    print "         d=3 and either D <= 3375000 or D 19-smooth";
    print "         d=4 and either D <= 4000000 or D 13-smooth)";
    print "  Estr (val is a string \"N:[a1,a2,a3,a4,a6]\" specifying the elliptic curve E to use, where N is the conductor)";
    print "  Kstr (val is a string \"D:[f0,f1,...,fd]\" specifying the number field K=Q[x]/(f0+f1*x+...+fd*x^d) to use, where D=|disc(K)|)";
    print "  cnum (val is a positive integer bound on the maximum number of point combinations to try; default is 5^6)";
    print "  cbound (val is a positive integer bound on the absolute value of integer coefficients used in point combinations; default is 5)";
    print "  jobs (val is a positive integer n specifying that this command is one of n jobs; default is 1)";
    print "  jobid (val is an integer in [0,n-1] specifying which job this is (automatically reduced modulo jobs); default is 0)";
    print "  verbose (val is a nonnegative integer specifying the verbosity level from 0 to 2; default is 0)";
    print "  Edump (val is 0 or 1; default 0, if 1 outputs a file N:[a1,a2,a3,a4,a6] for E matching bad prime criteria)";
    print "  Kdump (val is 0 or 1; default 0, if 1 outputs a file D:[f0,...,fd] for K matching bad (ramified) prime criteria)";
    print "  EKdump (val is 0 or 1; default 0, if 1 outputs a file N:[a1,a2,a3,a4,a6]:D:[f0,f1,...,fd]:r:rK for each pair E,K satsifying bad prime criteria)";
    print "";
	exit;
end if;

jobs := assigned jobs select atoi(jobs) else 1;
jobid := assigned jobid select atoi(jobid) else 0;
Nmax := assigned Nmax select atoi(Nmax) else 1000;
Dmax := assigned Dmax select atoi(Dmax) else 10000;
if assigned Kstr then
	assert assigned Estr;
	if not assigned P then P := sprint(PrimeDivisors(atoi(Split(Estr,":")[1])) cat PrimeDivisors(atoi(Split(Kstr,":")[1]))); end if;
end if;
P := assigned P select (P[1] eq "[" select atoii(P) else PrimesInInterval(1,atoi(P))) else [2];
P := Sort([p:p in Set(P)]); assert &and[IsPrime(p):p in P];
cbound := assigned cbound select atoi(cbound) else 5;
cnum := assigned cnum select atoi(cnum) else 19683;
radminp := assigned radminp select atoi(radminp) else 1;
if radminp lt 1 then radminp := 1; end if;
radmax := assigned radmax select atoi(radmax) else Floor(2^20/radminp);
pmax := Max(P);
pnum := assigned pnum select atoi(pnum) else 5;
verbose := assigned verbose select atoi(verbose) else 0;

pmaxval := func<p|p eq 2 select 20 else (p eq 3 select 10 else (p eq 5 select 9 else 4))>;

nf_file := "lmfdb_prym_nf.txt";	// Sorted list of number fields |D|:[f_0,f_1,...,f_{d-1},1] of degree <= 4 over which to look for branch points
ec_file := "lmfdb_prym_ec.txt"; // list of elliptic curves N:[a1,a2,a3,a4,a6] not already in the Cremona database to use

U<x,y,z> := PolynomialRing(Rationals(), 3);

// B_pt holds upper bounds for EC point search, depending on the degree of the field.
B_pt := AssociativeArray(); B_pt[2] := 100; B_pt[3] := 50; B_pt[4] := 25;
B_sat := 10;				// Upper bound on primes used in saturation step.
Amax := 2^20;				// Upper bound on target conductors of Prym (we skip covers we can prove exceed this)
Cmax := 2000;				// Upper bound (in characters) on size of equations/invariants appearing in covers
							// Only relevant for hyperelliptic curves, used to avoid spending time on computations

// Helper functions S_comb and T_comb below select coefficients c_i for integer linear combinations \sum c_i P_i that will be used
// to select ramification points.  Each P_i listed in L should be a (possibly torsion) generator of the MW group of E or its base change to K.
// We adjust cbound on the integers c_i depending on the number of generators to keep the number of combinations below cnum,
// but we will never drop the bound below 1 (which may mean more than cnum combinations when the number of generators is large)
function S_comb(L)
	b := cbound+1;
	repeat
		b -:= 1;
		if b eq 0 then
			c := [{0..1}:P in L];
		else
			c := [(ord eq 0) or (ord gt 2*b) select {-b..b} else {0..ord-1} where ord := Order(P) : P in L ];
		end if;
	until b eq 0 or #CartesianProduct(c) le cnum;
	return CartesianProduct(c);
end function;

// T_comb is used for the case K=Q, where we will be choosing 3 points on E and we want to avoid duplicating choices
function T_comb(L)
	b := cbound+1;
	repeat
		b -:= 1;
		c := [ (ord eq 0) or (ord gt 2*b) select {0..b} else {0..ord-1} where ord := Order(P) : P in L ];
	until b eq 1 or Binomial(#CartesianProduct(c),3) le cnum;
	return Subsets(Set(CartesianProduct(c)),3);
end function;

function PickEvenModel(L,E)
    EE := [ReducedMinimalWeierstrassModel(Genus1CurveFromEvenModel(C)):C in L];
    I := [j:j in [1..#EE]];
    I := ReduceToReps(I,func<j,k|IsIsomorphic(EE[j],EE[k])>);
    D := LCM([Integers()|Discriminant(EE[j]):j in I] cat [Integers()!Discriminant(E)]);
    p := 2;
    while p lt 256 and #I gt 1 do
        p := NextPrime(p);
        if D mod p eq 0 then continue; end if;
        F := GF(p); n := #RationalPoints(ChangeRing(E,F));
        I := [j:j in I|#RationalPoints(ChangeRing(EE[j],F)) eq n];
    end while;
    return L[1];
end function;

field_degrees := {1,2,3,4};	// Allowable degrees for ramification points

if not assigned Kstr then
	// Load number fields from nf_file
	if not assigned Kfile then
		t := Cputime();
		RX<x> := PolynomialRing(Rationals());
		Ks := Split(Read(nf_file));
		lastD := 0;
		I := [];
		for i in [1..#Ks] do
			s := Ks[i];
			j := Index(s,":");
			D := Abs(atoi(s[1..j-1])); assert D ge lastD; lastD := D;
			if D gt Dmax then break; end if; // assumes file is sorted!
			c := atoii(s[j+1..#s]);
			if not #c-1 in field_degrees then continue; end if;
			T := PrimeDivisors(D);
			if not T subset P or #T gt pnum or &*[Integers()|p:p in T|p gt radminp] gt radmax then continue; end if;
			Append(~I,i);
		end for;
		Ks := Ks[I];
		fprintf "/dev/stderr","%o:Loaded %o number fields in %.3os\n", jobid, #Ks, Cputime()-t;
	else
		Ks := Split(Read(Kfile));
	end if;
else
	Ks := [Kstr];		// use number field specififed on the command line
end if;

if assigned Kdump then
	fp := Open(Kdump,"w");
	for Kstr in Ks do Puts(fp,Kstr); end for;
	Flush(fp);
	exit;
end if;

Kps := [Set(PrimeDivisors(atoi(Split(k,":")[1]))):k in Ks];
Kfs := [atoii(Split(k,":")[2]):k in Ks];

if not assigned Estr then
	if not assigned Efile then
		t := Cputime();
		conductors := {N:N in [11..Min(Nmax,499999)]|Q subset P and #Q le pnum and &*[Integers()|p:p in Q|p gt radminp] le radmax where Q:=PrimeDivisors(N)};
		ECDB := CremonaDatabase();
		Es := &cat[[Sprintf("%o:%o",Conductor(E),sprint(Coefficients(E))):E in EllipticCurves(ECDB,N)]:N in conductors];
		if Nmax gt 500000 then
			S := Split(Read(ec_file));
			Es cat:= [r:r in S|N le Nmax and Q subset P and #P le pnum and &*[Integers()|p:p in Q|p gt radminp] le radmax where Q:= [p:p in PrimeDivisors(N)|p ne 2] where N:=atoi(Split(r,":")[1])];
		end if;
		fprintf "/dev/stderr","%o:Computed set of %o elliptic curves in %.3os\n", jobid, #Es, Cputime()-t;
	else
		Es := Split(Read(Efile));	// use elliptic curves listed in user-supplied file
	end if;
else
	Es := [Estr];		// use elliptic curve specified on the command line
end if;

if assigned Edump and Edump ne "0" then for Estr in Es do print Estr; end for; exit; end if;

cnt := -1;
fs := {};
for Estr in Es do // for each elliptic curve E
	cnt +:= 1;
	if (cnt-jobid) mod jobs ne 0 then continue; end if;
	if verbose ge 0 then fprintf "/dev/stderr","%o:Working on elliptic curve %o\n", jobid, Estr; end if;
	Estart := Cputime();
	E := ":" in Estr select EllipticCurve(atoii(Split(Estr,":")[2])) else EllipticCurve(Estr);
	NE := Conductor(E); eprimes := PrimeDivisors(NE);
	MW, phi := MordellWeilGroup(E:HeightBound:=12); // reduce height bound from default of 15 to 12 to keep the effort reasonable
	MW_Q := [ E | phi(g) : g in Generators(MW) ];
	r := #MW_Q;
	T2:=[E!0] cat [phi((Order(P) div 2)*P):P in Generators(MW)|Order(P) ne 0 and Order(P) mod 2 eq 0];
	if #T2 eq 3 then T2[4]:=T2[2]+T2[3]; end if;
	if verbose ge 0 then fprintf "/dev/stderr","%o:Computed Mordell-Weil group with %o generators and #E(Q)[2]=%o for %o in %.3os\n", jobid, r, #T2, Estr, Cputime()-Estart; end if;
	p_E := Set(PrimeDivisors(NE));
	I := r eq 0 select [i:i in [1..#Ks]|#Kfs[i] gt 3] else [1..#Ks]; // For r = 0 we want the deg(K) >= 3, meaning #Kfs[i] > 3 (cubic has 4 coeffs)
	I := [i:i in I|#s le pnum and &*[Integers()|p:p in s|p gt radminp] le radmax where s:=(p_E join Kps[i])];
	if verbose ge 0 then fprintf "/dev/stderr","%o:Selected %o number fields for elliptic curve %o\n",jobid,#I,Estr; end if;

	Eout:=0; Kcnt:=0; ctot:=0; xtot:=0;
	for Ki in I do // for each number field K
		Kstr:=Ks[Ki];
		Kstart := Cputime();
		if not assigned EKdump and verbose ge 0 then fprintf "/dev/stderr","%o:Working on number field %o for elliptic curve %o\n", jobid, Kstr, Estr; end if;
		K := NumberField(PolynomialRing(QQ)!Kfs[Ki]:DoLinearExtension); // DoLinearExtension lets us include Q as the trivial extension
		EK := ChangeRing(E, K);
		if Degree(K) gt 1 then
			Pts_K := SetToSequence(Points(EK : Bound := B_pt[Degree(K)]));
			// For K != Q we require at least one rational K-points that is not defined over Q
			if &and[X[1] in QQ and X[2] in QQ and X[3] in QQ:X in Pts_K] then
				if (not assigned EKdump and verbose ge 0) or verbose ge 1 then fprintf "/dev/stderr","%o:Finished number field %o for elliptic curve %o finding no new K-points (r=%o) after %.3os\n", jobid, Kstr, Estr, r, Cputime()-Kstart; end if;
				continue;
			end if;
			if assigned EKdump then
				Kcnt +:=1;
				print Sprintf("%o:%o:%o:%.3os",jobid,Estr,Kstr,Cputime()-Kstart);
				continue;
			end if;
			Pts_K cat:= [ EK | x:x in MW_Q];
			MW_K := Saturation(Pts_K, B_sat);
			rK := #MW_K;
			assert rK ge r;
		else
			if assigned EKdump and EKdump ne "0" then
				print Sprintf("%o:%o:%.3os",jobid,Estr,Kstr,Cputime()-Kstart);
				continue;
			end if;
			MW_K := [ EK | phi(g) : g in Generators(MW)];
			rK := #MW_K;
		end if;
		Kcnt +:= 1;

		L, rts := NormalClosure(K);
		EL := ChangeRing(E, L);
		if Degree(K) eq 1 then
			P4 := Identity(E);
		elif Degree(K) lt 4 then
			P4 := Identity(EL);
		end if;

		if Degree(K) eq 1 then
			coeff_set := T_comb(MW_Q);
		elif Degree(K) eq 2 then
			coeff_set := S_comb([* P : P in MW_K *] cat [* P : P in MW_Q *]);
		elif Degree(K) ge 3 then
			coeff_set := S_comb(MW_K);
		end if;

		if verbose ge 0 then fprintf "/dev/stderr","%o:Computed coefficient set of size %o for number field %o for elliptic curve %o with MWQinv=%o and MWKinv=%o in %.3os\n", jobid, #coeff_set, Kstr, Estr, sprint([Order(P):P in MW_Q]), sprint([Order(P):P in MW_K]), Cputime()-Kstart; end if;
		Qstrs := {};
		Kout := 0; ccnt := 0; xcnt := 0;
		for c in coeff_set do // for each integer linear combination of generators
			ccnt +:= 1;
			if verbose gt 0 then fprintf "/dev/stderr","%o:Working on coefficients %o (%o of %o) for number field %o for elliptic curve %o\n", jobid, sprint(c), ccnt, #coeff_set, Kstr, Estr; end if;
			Cstart := Cputime();
			if Degree(K) eq 1 then
				cc := [x:x in c];
				Ps := [ &+[cc[i][j]*phi(MW.j) : j in [1..r]] : i in [1..3] ];
				P1, P2, P3 := Explode(Ps);
				Nx := Numerator(x)*Denominator(x) where x := (P1[1] - P2[1])*(P1[1] - P3[1])*(P2[1] - P3[1]);
				Ny := Numerator(x)*Denominator(x) where x := (P1[2] - P2[2])*(P1[2] - P3[2])*(P2[2] - P3[2]);
				N := GCD(Nx, Ny);
			elif Degree(K) eq 2 then
				PK := &+[c[i]*MW_K[i] : i in [1..rK]];
				PL := [ EL![  Evaluate(PolynomialRing(Rationals())!Eltseq(PK[i]), rts[j]) : i in [1..3]] : j in [1..2]];
				P1, P2 := Explode(PL);
				P3 := EL!&+[c[rK+i]*phi(MW.i) : i in [1..r]];
				Nx := Numerator(x)*Denominator(x) where x := Norm( (P1[1] - P2[1])*(P1[1] - P3[1]) );
				Ny := Numerator(x)*Denominator(x) where x := Norm( (P1[2] - P2[2])*(P1[2] - P3[2]) );
				N := GCD(Nx, Ny);
			elif Degree(K) eq 3 then
				PK := &+[c[i]*MW_K[i] : i in [1..rK]];
				PL := [ EL![  Evaluate(PolynomialRing(Rationals())!Eltseq(PK[i]), rts[j]) : i in [1..3]] : j in [1..3]];
				P1, P2, P3 := Explode(PL);
				Nx := Numerator(x)*Denominator(x) where x := Norm(P1[1] - P2[1]);
				Ny := Numerator(x)*Denominator(x) where x := Norm(P1[2] - P2[2]);
				N := GCD(Nx, Ny);
			elif Degree(K) eq 4 then
				t:=Cputime();
				PK := &+[c[i]*MW_K[i] : i in [1..rK]];
				PL := [ EL![  Evaluate(PolynomialRing(Rationals())!Eltseq(PK[i]), rts[j]) : i in [1..3]] : j in [1..4]];
				P1, P2, P3, P4 := Explode(PL);
				Nx := Numerator(x)*Denominator(x) where x := Norm(P1[1] - P2[1]);
				Ny := Numerator(x)*Denominator(x) where x := Norm(P1[2] - P2[2]);
				N := GCD(Nx, Ny);
			end if;
			if #{ EL | P1,P2,P3,P4} ne 4 or N eq 0 then
				if verbose gt 0 then fprintf "/dev/stderr","%o:Ramification points not distinct, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;

			// Analyse the set of odd primes where some points are colliding.
			T := TrialDivision(N, pmax);
			p_collide := { p[1] : p in T };
			bad_primes := (p_collide join p_E);
			odd_bad_primes := bad_primes diff {2};
			if &*[Integers()|r[1]^r[2]:r in T] ne N or not(odd_bad_primes subset P) or
			   #odd_bad_primes gt pnum or &*[Integers()|p:p in odd_bad_primes|p gt radminp] gt radmax then
			    if verbose gt 0 then fprintf "/dev/stderr","%o:Bad set of colliding primes for %o digit N, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(Ceiling(Log(10,Abs(N)))), sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;
			Psum := E!(P1 + P2 + P3 + P4);
			b, Q0 := IsDivisibleBy(Psum, 2);	// Check if P1+P2+P3+P4 is divisible by 2 for later Riemann-Roch calculation
			if not(b) then
				if verbose gt 0 then fprintf "/dev/stderr","%o:Psum not divisible by 2, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;

			Dnum := &+[Divisor(P) : P in [P1,P2,P3,P4]];
			Inum := Ideal(Dnum);
			InumQ := ideal<CoordinateRing(Ambient(E)) | GroebnerBasis(Inum) >;
			DnumQ := Divisor(E, InumQ);

			for i:=1 to #T2 do // for each 2-torsion point of E
				if verbose gt 0 then fprintf "/dev/stderr","%o:Working on T2[%o]=%o in coefficients %o (%o of %o) for number field %o for elliptic curve %o\n", jobid, i, sprint(T2[i]), sprint(c), ccnt, #coeff_set, Kstr, Estr; end if;
				Q := Q0+T2[i];
				Qstr := sprint(InumQ) cat ":" cat sprint(Q);
				if Qstr in Qstrs then continue; else Include(~Qstrs,Qstr); end if;
				xcnt +:= 1;
				if verbose gt 1 then tcover := Cputime(); end if;
				sts, X := Genus3DoubleCover(E,DnumQ,Q:SizeBound:=Cmax);
				if verbose gt 1 then fprintf "/dev/stderr","%o:Genus3DoubleCover returned %o for coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sts, sprint(c), i, Kstr, Estr, Cputime()-tcover; tpost := Cputime(); end if;
				if sts lt 0 then
					if verbose ge 0 then fprintf "/dev/stderr","%o:Error %o returned by Genus3DoubleCover for coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sts, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
				    continue;
				end if;
				hyp := Type(X) eq CrvHyp;
				g := 3;
				ctype := hyp select "hyperelliptic" else "SPQ";
				if hyp then
				    L := EvenModels(X);
				    if #L gt 0 then
    					Y := #L eq 1 select L[1] else PickEvenModel(L,E);
						X := IntegralSimplifiedModel(Genus2CurveFromEvenModel(Y)); g := 2; ctype := "genus 2";
					else
						X := IntegralSimplifiedModel(X);
					end if;
				else
					b,Y := Genus2CurveFromEvenModel(X);
					if b then X := IntegralSimplifiedModel(Y); g := 2; hyp := true; ctype := "genus 2"; end if;
				end if;
				fdisc := Abs(Integers()!Discriminant(X));
				if Log(10,fdisc) gt 5000 then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Large %o digit discriminant for %o curve, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, #sprint(fdisc), ctype, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
				    continue;
				end if;
				disc_primes := {Integers()|p:p in bad_primes|fdisc mod p eq 0};
				xdisc := fdisc div &*[Integers()|p^Valuation(fdisc,p):p in disc_primes];
				T := TrialDivision(xdisc, Amax);
				if &*[Integers()|r[1]^r[2]:r in T] ne xdisc then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Extraneous large prime of bad reduction for %o curve with %o digit discriminant, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, ctype, #sprint(fdisc), sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
					continue;
				end if;
				disc_primes join:= {r[1]:r in T};
				if verbose gt 1 then fprintf "/dev/stderr","%o:Initial post processing for coefficients %o(%o) for number field %o for elliptic curve %o took %.3os\n", jobid,  sprint(c), i, Kstr, Estr, Cputime()-tpost; tpost := Cputime(); end if;
				if hyp then
					X := ReducedMinimalWeierstrassModel(X);
					f := CoefficientString(X);
					fdisc := Abs(Integers()!Discriminant(X));
				else
					// minimize plane quartic prime by prime to avoid calling MinimizeReducePlaneQuartic, which might get stuck
					f := DefiningPolynomial(X);
					for p in disc_primes do
						if Valuation(fdisc,p) ge 12 then
							f := MinimizePlaneQuartic(f,p); fdisc := Abs(TernaryFormDiscriminant(f));
						end if;
					end for;
					n := #disc_primes;
					disc_primes := [p:p in disc_primes|fdisc mod p eq 0];
					if verbose gt 0 and #disc_primes lt n then fprintf "/dev/stderr","%o:Minimization removed a bad prime for coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
					f := CoefficientString(Genus3Curve(f));
				end if;
				if verbose gt 1 then fprintf "/dev/stderr","%o:Final post processing for coefficients %o(%o) for number field %o for elliptic curve %o took %.3os\n", jobid,  sprint(c), i, Kstr, Estr, Cputime()-tpost; end if;
				if f in fs then continue; else Include(~fs,f); end if;
				if #disc_primes gt pnum+2 or
				   &*[Integers()|p:p in disc_primes|(g eq 2 or not p in eprimes) and Valuation(fdisc,p) lt 12] gt Amax then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Too many extra primes of bad reduction %o %o, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(disc_primes), sprint([Valuation(fdisc,p):p in disc_primes]), sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
				    continue;
				end if;
				Kout+:=1; Eout+:=1;
				print Sprintf("%o:%o:%o:%o:%o:%o:%.3o",jobid,sts,g,f,Estr,Kstr,Cputime()-Cstart);
				if verbose gt 0 and #T2 gt 1 then fprintf "/dev/stderr","%o:Finished T2[%o]=%o for coefficients %o (%o of %o) for number field %o for elliptic curve %o in %.3os\n", jobid, i, sprint(T2[i]), sprint(c), ccnt, #coeff_set, Kstr, Estr, Cputime()-Cstart; end if;
			end for;
			if verbose gt 0 then fprintf "/dev/stderr","%o:Finished coefficients %o (%o of %o) for number field %o for elliptic curve %o in %.3os\n", jobid, sprint(c), ccnt, #coeff_set, Kstr, Estr, Cputime()-Cstart; end if;
		end for;
		ctot +:= ccnt; xtot +:= xcnt;
		if verbose ge 0 then fprintf "/dev/stderr","%o:Finished number field %o for elliptic curve %o testing %o coefficients, %o covers, and generating %o Pryms in %.3os\n", jobid, Kstr, Estr, ccnt, xcnt, Kout, Cputime()-Kstart; end if;
	end for;
	if verbose ge 0 then fprintf "/dev/stderr","%o:Finished elliptic curve %o testing %o number fields (of which %o passed), %o coefficients, %o covers, generating %o Pryms in %.3os\n", jobid, Estr, #I, Kcnt, ctot, xtot, Eout, Cputime()-Estart; end if;
end for;
exit;
