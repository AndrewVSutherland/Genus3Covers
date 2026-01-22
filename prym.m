verbose := assigned verbose select atoi(verbose) else 0;
split := assigned split select atoi(split) else 0;
if assigned Kstr then assert assigned Estr; single := true; else single := false; end if;
jobs := assigned jobs select atoi(jobs) else 1;
jobid := assigned jobid select atoi(jobid) else 0;
Nmax := assigned Nmax select atoi(Nmax) else 1000;
Dmax := assigned Dmax select atoi(Dmax) else 10000;
Pstr := assigned P select P else "[2]";
P := assigned P select (P[1] eq "[" select atoii(P) else PrimesInInterval(1,atoi(P))) else [2];
c_bound := assigned cbound select atoi(cbound) else 5;
c_num := assigned cnum select atoi(cnum) else 15625;
radmax := assigned radmax select atoi(radmax) else 2^20;
p_allowed := {p:p in P| p le radmax};
p_max := Max(p_allowed);
p_maxproduct := Min(&*p_allowed,radmax);
p_maxnumber := Min(#p_allowed,5);

pmaxval := func<p|p eq 2 select 20 else (p eq 3 select 10 else (p eq 5 select 9 else 4))>;

nf_file := "lmfdb_prym_nf.txt";	// Sorted list of number fields |D|:[f_0,f_1,...,f_{d-1},1] over which to look for branch points
ec_file := "lmfdb_prym_ec.txt"; // list of elliptic curves N:[a1,a2,a3,a4,a6] not in Cremona database to use as base

// (TODO): biquadratic case, geometrically hyperelliptic curves, twisting
U<x,y,z> := PolynomialRing(Rationals(), 3);

B_pt := AssociativeArray(); B_pt[2] := 100; B_pt[3] := 50; B_pt[4] := 25;	// Upper bound for EC point search, dependending on the degree of the field.
B_sat := 10;	// Upper bound for saturation step.

function S_comb(L) // Coefficients c_i to try for linear combinations \sum c_i P_i where P_i are points on the elliptic curve, as a function of the number of generators.
	// This function takes as input a list of curves and outputs a list of sets for the coefficients c_i. (This is, so that for a point of order n we can take {0..n-1} rather than the larger default interval if n is small.
	b := c_bound+1;
	repeat
		b -:= 1;
		c := [ (ord eq 0) or (ord gt 2*b) select {-b..b} else {0..ord-1} where ord := Order(P) : P in L ];
	until b eq 1 or #CartesianProduct(c) le c_num;
	return CartesianProduct(c);
end function;

function T_comb(L)
	b := c_bound+1;
	repeat
		b -:= 1;
		c := [ (ord eq 0) or (ord gt 2*b) select {0..b} else {0..ord-1} where ord := Order(P) : P in L ];
	until b eq 1 or Binomial(#CartesianProduct(c),3) le c_num;
	return Subsets(Set(CartesianProduct(c)),3);
end function;
field_degrees := {1,2,3,4};	// Allowable degrees for ramification points (may cause program to ignore part of the input data from fields_file).

// Load number fields from the file
pset := {2} join p_allowed;
if not assigned Kstr then
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
			if not T subset pset or #T gt p_maxnumber or &*T gt p_maxproduct then continue; end if;
			Append(~I,i);
		end for;
		fprintf "/dev/stderr","%o:Loaded %o number fields in %.3os\n", jobid, #I, Cputime()-t;
		Ks := Ks[I];
	else
		Ks := Split(Read(Kfile));
		I := [1..#Ks];
	end if;
else
	I := [1]; Ks := [Kstr];
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
		conductors := {N:N in [11..Min(Nmax,499999)]|P subset p_allowed and #P le p_maxnumber and &*P le p_maxproduct where P:=PrimeDivisors(N)};
		ECDB := CremonaDatabase();
		Es := &cat[[Sprintf("%o:%o",Conductor(E),sprint(Coefficients(E))):E in EllipticCurves(ECDB,N)]:N in conductors];
		if Nmax gt 500000 then
			S := Split(Read(ec_file));
			Es cat:= [r:r in S|N le Nmax and P subset p_allowed and #P le p_maxnumber and &*P le p_maxproduct where P:= PrimeDivisors(N) where N:=atoi(Split(r,":")[1])];
		end if;
		fprintf "/dev/stderr","%o:Computed set of %o elliptic curves in %.3os\n", jobid, #Es, Cputime()-t;
	else
		Es := Split(Read(Efile));
	end if;
else
	Es := [Estr];
end if;

if assigned Edump and Edump ne "0" then for Estr in Es do print Estr; end for; exit; end if;

cnt := -1;
rstrs := [];
fs := {};
for Estr in Es do
	cnt +:= 1;
	if (cnt-jobid) mod jobs ne 0 then continue; end if;
	fprintf "/dev/stderr","%o:Working on elliptic curve %o\n", jobid, Estr;
	Estart := Cputime();
	E := ":" in Estr select EllipticCurve(atoii(Split(Estr,":")[2])) else EllipticCurve(Estr);
	NE := Conductor(E); eprimes := PrimeDivisors(NE);
	MW, phi := MordellWeilGroup(E:HeightBound:=12); // reduce height bound from default of 15 to 12 to keep the effort reasonable
	MW_Q := [ E | phi(g) : g in Generators(MW) ];
	r := #MW_Q;
	T2:=[E!0] cat [phi((Order(P) div 2)*P):P in Generators(MW)|Order(P) ne 0 and Order(P) mod 2 eq 0];
	if #T2 eq 3 then T2[4]:=T2[2]+T2[3]; end if;
	fprintf "/dev/stderr","%o:Computed Mordell-Weil group with %o generators and #E(Q)[2]=%o for %o in %.3os\n", jobid, r, #T2, Estr, Cputime()-Estart;
	p_E := Set(PrimeDivisors(NE));
	I := r eq 0 select [i:i in [1..#Ks]|#Kfs[i] gt 3] else [1..#Ks]; // For r = 0 we want the deg(K) >= 3
	I := [i:i in I|#s le p_maxnumber and &*s le p_maxproduct where s:=p_E join Kps[i]];
	if not single then fprintf "/dev/stderr","%o:Selected %o number fields for elliptic curve %o\n",jobid,#I,Estr; end if;

	Eout:=0; Kcnt:=0;
	for Ki in I do
		Kstr:=Ks[Ki];
		Kstart := Cputime();
		if verbose gt 0 or not single then fprintf "/dev/stderr","%o:Working on number field %o for elliptic curve %o\n", jobid, Kstr, Estr; end if;
		K := NumberField(PolynomialRing(QQ)!Kfs[Ki]:DoLinearExtension); // DoLinearExtension handles Q
		EK := ChangeRing(E, K);
		if Degree(K) gt 1 then
			Pts_K := SetToSequence(Points(EK : Bound := B_pt[Degree(K)]));
			// There need to be K-points that are not defined over Q
			if &and[X[1] in QQ and X[2] in QQ and X[3] in QQ:X in Pts_K] then
				if verbose gt 0 then fprintf "/dev/stderr","%o:No new K-points (r=%o) for number field %o for elliptic curve %o after %.3os\n", jobid, r, Kstr, Estr, Cputime()-Kstart; end if;
				continue;
			end if;
			Pts_K cat:= [ EK | x:x in MW_Q];
			MW_K := Saturation(Pts_K, B_sat);
			rK := #MW_K;
			assert rK ge r;
			// There need to be more points over K than over Q
			if rK eq r then
				if verbose gt 0 then fprintf "/dev/stderr","%o:Not enough K-points (r=%o, rK=%o) for number field %o for elliptic curve %o after %.3os\n", jobid, r, rK, Kstr, Estr, Cputime()-Kstart; end if;
				continue;
			end if;
		else
			MW_K := [ EK | phi(g) : g in Generators(MW)];
			rK := #MW_K;
		end if;
		Kcnt +:= 1;
		if assigned EKdump and EKdump ne "0" then
			print Sprintf("%o:%o:%o:%o:%.3os",Estr,Kstr,r,rK,Cputime()-Kstart);
			continue;
		end if;

		L, rts := NormalClosure(K);
		EL := ChangeRing(E, L);
		if Degree(K) eq 1 then
			P4 := Identity(E);
		elif Degree(K) lt 4 then
			P4 := Identity(EL);	// Except for degree 4, pick the last point to be the identity.
		end if;

		if Degree(K) eq 1 then
			coeff_set := T_comb(MW_Q);
		elif Degree(K) eq 2 then
			coeff_set := S_comb([* P : P in MW_K *] cat [* P : P in MW_Q *]);
		elif Degree(K) ge 3 then
			coeff_set := S_comb(MW_K);
		end if;

		fprintf "/dev/stderr","%o:Computed coefficient set of size %o for number field %o for elliptic curve %o with MWQinv=%o and MWKinv=%o in %.3os\n", jobid, #coeff_set, Kstr, Estr, sprint([Order(P):P in MW_Q]), sprint([Order(P):P in MW_K]), Cputime()-Kstart;
		Qstrs := {};
		Kout := 0; ccnt := 0;
		for c in coeff_set do
			ccnt +:= 1;
			if verbose gt 0 then fprintf "/dev/stderr","%o:Working on coefficients %o (%o of %o) for number field %o for elliptic curve %o\n", jobid, sprint(c), ccnt, #coeff_set, Kstr, Estr; end if;
			Cstart := Cputime();
			if Degree(K) eq 1 then
				cc := [x:x in c]; assert #c eq 3;
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
				// TODO: check divisibility by 2 for P1+P2+P3+P4 for the Riemann-Roch problem to be solvable.
			end if;
			if #{ EL | P1,P2,P3,P4} ne 4 or N eq 0 then
				if verbose gt 0 then fprintf "/dev/stderr","%o:Ramification points not distinct, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;
			// if not(2 in p_allowed) and Degree(K) eq 3 and not(IsZero(bar2(PK))) then continue; end if;
			// Analyse the set of primes where some points are colliding.
			T := TrialDivision(N, p_max);
			p_collide := { p[1] : p in T };
			bad_primes := p_collide join p_E;
			if &*[Integers()|r[1]^r[2]:r in T] ne N or not(bad_primes subset pset) or #bad_primes gt p_maxnumber or &*bad_primes gt p_maxproduct then
			    if verbose gt 0 then fprintf "/dev/stderr","%o:Bad set of colliding primes for %o digit N, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(Ceiling(Log(10,Abs(N)))), sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;
			Psum := E!(P1 + P2 + P3 + P4);
			b, Q := IsDivisibleBy(Psum, 2);	// Check if P1+P2+P3+P4 is divisible by 2 for later RR calculation. (TODO: improve this in case of degree <= 3 by choosing P4 to automatically satisfy this)
			if not(b) then
				if verbose gt 0 then fprintf "/dev/stderr","%o:Psum not divisible by 2, skipping coefficients %o for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), Kstr, Estr, Cputime()-Cstart; end if;
				continue;
			end if;

			Dnum := &+[Divisor(P) : P in [P1,P2,P3,P4]];
			Inum := Ideal(Dnum);
			InumQ := ideal<CoordinateRing(Ambient(E)) | GroebnerBasis(Inum) >;
			DnumQ := Divisor(E, InumQ);

			// Loop over Q+T for T 2-torsion point on Q
			Q0:=Q;
			for i:=1 to #T2 do
				if verbose gt 0 then fprintf "/dev/stderr","%o:Working on T2[%o]=%o in coefficients %o (%o of %o) for number field %o for elliptic curve %o\n", jobid, i, sprint(T2[i]), sprint(c), ccnt, #coeff_set, Kstr, Estr; end if;
				Q := Q0+T2[i];
				Qstr := sprint(InumQ) cat ":" cat sprint(Q);
				if Qstr in Qstrs then continue; else Include(~Qstrs,Qstr); end if;
				D := DnumQ - 2*Divisor(Q) - 2*Divisor(Zero(E));

				// Use Riemann-Roch to find a function f with odd poles at P1, P2, P3, and P4.
				b, f := IsPrincipal(D);
				assert b;
				// Extend the function field with sqrt(f)
				FF<x,y> := FunctionField(E);
				FF2<y>, rho_alg := AlgorithmicFunctionField(FF);
				_<x> := BaseField(FF2);
				f2 := rho_alg(f);
				R<Z> := PolynomialRing(FF2);
				KF<a> := ext<FF2 | Z^2 - f2>;

				// Next find equation for canonical image, or hyperelliptic equation.
				LF := AbsoluteFunctionField(KF);
				g := DefiningPolynomial(LF);
				if #sprint(g) gt 2000 then  // If the equation for g is too horrible give up now
					fprintf "/dev/stderr","%o:Defining polynomial with %o characters too big, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, #sprint(g), sprint(c), i, Kstr, Estr, Cputime()-Cstart;
					continue;
				end if;
				C0 := Curve(AffineSpace(Parent(g)), g);
				ghyp, X := IsGeometricallyHyperelliptic(C0);
				if ghyp then
					spq := false;
					hyp, C := IsHyperelliptic(C0);
					d := 0;
					if not hyp then
						d := Integers()!Discriminant(MinimalModel(X));
						T := TrialDivision(d,p_max);
						Tbad := {r[1]:r in T} join bad_primes; 
						if &*[Integers()|r[1]^r[2]:r in T] ne d or #Tbad gt p_maxnumber or &*Tbad gt p_maxproduct then
							if verbose gt 0 then fprintf "/dev/stderr","%o:Geometrically hyperelliptic curve whose conic introduces to many or too large bad primes, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
							continue;
						end if;
						d := SquareFree(d);
						for c in [1,-1,2,-2] do
							ghyp, C := IsHyperelliptic(ChangeRing(C0,QuadraticField(c*d)));
							if ghyp then d:=c*d; break; end if;
						end for;
						if not ghyp then // how does this happen?
							fprintf "/dev/stderr","%o:Geometrically hyperelliptic curve not hyperelliptic over Q(sqrt(disc(X)) where X is the conic with discriminant D=+/-1,2*%o, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, Abs(d), sprint(c), i, Kstr, Estr, Cputime()-Cstart;
							continue;
						end if;
						C := SimplifiedModel(C);
						f := HyperellipticPolynomials(C);
						f *:= LCM([Denominator(c):c in Coefficients(f)])^2;
						C := HyperellipticCurve(f);
						fdisc := Abs(Integers()!Norm(Discriminant(C)));
					end if;
					C := SimplifiedModel(C);
					f := HyperellipticPolynomials(C);
					f *:= LCM([Denominator(c):c in Coefficients(f)])^2;
					C := HyperellipticCurve(f);
					fdisc := (hyp select 1 else d^2)*Abs(Integers()!Norm(Discriminant(C)));
					f := d eq 0 select CoefficientString(C) else sprint([[d]] cat [Eltseq(c):c in Coefficients(f)]);
				else
					hyp := false; spq := true;
					rho_can := CanonicalMap(C0);
					C := CanonicalImage(C0, rho_can);
					assert Genus(C) eq 3;
					f := CoefficientString(C);
					fdisc := Abs(Integers()!CurveDiscriminant(C));
				end if;
				ctype := hyp select "hyperelliptic" else (ghyp select "geometrically hyperelliptic" else "plane quartic");
				if Log(10,fdisc) gt 5000 then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Large %o digit discriminant for %o curve, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, #sprint(fdisc), ctype, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
				    continue;
				end if;
				disc_primes := {p:p in bad_primes|fdisc mod p eq 0};
				xdisc := fdisc div &*[p^Valuation(fdisc,p):p in disc_primes];
				extra_primes := xdisc gt 1 select (b select {p} else {p:p in pset|xdisc mod p eq 0} where b,p:=IsPrimePower(xdisc)) else {Integers()|};
				if &*[Integers()|p^Valuation(xdisc,p):p in extra_primes] ne xdisc then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Extraneous large prime of bad reduction for %o curve with %o digit discriminant, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, ctype, #sprint(fdisc), sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
					continue;
				end if;
				disc_primes join:= extra_primes;
				// Don't try to minimize until we are sure we can easily factor the discriminant
				if hyp then
					C := ReducedMinimalWeierstrassModel(C);
					f := CoefficientString(C);
					fdisc := Abs(Integers()!Discriminant(C));
				elif ghyp then
					// We current make no attempt to minimize geometrically hyperelliptic curves
				else
					f := DefiningPolynomial(C);
					for p in disc_primes do if Valuation(fdisc,p) ge 12 then f := MinimizePlaneQuartic(f,p); fdisc := Abs(TernaryFormDiscriminant(f)); end if; end for;
					n := #disc_primes;
					disc_primes := [p:p in disc_primes|fdisc mod p eq 0];
					if verbose gt 0 and #disc_primes lt n then fprintf "/dev/stderr","%o:Minimization removed a bad prime for coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
					f := CoefficientString(Genus3Curve(f));
				end if;
				assert IsDivisibleBy(fdisc,NE);
				if f in fs then continue; else Include(~fs,f); end if;
				if #disc_primes gt p_maxnumber+2 or &*[Integers()|p:p in disc_primes|not p in eprimes and Valuation(fdisc,p) lt 12] gt p_maxproduct then
					if verbose gt 0 then fprintf "/dev/stderr","%o:Too many extra primes of bad reduction %o %o, skipping coefficients %o(%o) for number field %o for elliptic curve %o after %.3os\n", jobid, disc_primes, sprint([Valuation(fdisc,p):p in disc_primes]), sprint(c), i, Kstr, Estr, Cputime()-Cstart; end if;
				    continue;
				end if;
				rstr := Sprintf("%o:%o:%o",jobid,f,Estr);
				if not rstr in rstrs then
					Include(~rstrs,rstr);
					Kout+:=1; Eout+:=1;
					N := fdisc div NE;
					badp := Sort([p:p in disc_primes]);
					emin := [NE mod p ne 0 and Valuation(N,p) in [1..11] select 1 else 0:p in badp];
					emax := [Min(Valuation(N,p),pmaxval(p)):p in badp];
					if hyp or spq then C := Genus3Curve(f); end if;
					inv := ghyp select NormalizedShiodaInvariants(C) else DixmierOhnoInvariants(C:IntegralNormalization);
					if not ghyp then assert fdisc eq Abs(inv[13]); end if;
					s := Sprintf("%o/%o",f,CoefficientString(E));
					// todo add hashes for geometrically hyperelliptic curves
					if hyp or spq then hash, qhash := TraceTwistHash(s); else hash := 0; qhash := 0; end if;
					print Sprintf("%o:%o:%o(%o):%o:%o:%o:%o:%o:%o:%.3o",rstr,Kstr,sprint(c),i,sprint(badp),sprint(emin),sprint(emax),hash,qhash,sprint(inv),Cputime()-Cstart);
				end if;
				if verbose gt 0 and #T2 gt 1 then fprintf "/dev/stderr","%o:Finished T2[%o]=%o for coefficients %o (%o of %o) for number field %o for elliptic curve %o in %.3os\n", jobid, i, sprint(T2[i]), sprint(c), ccnt, #coeff_set, Kstr, Estr, Cputime()-Cstart; end if;
			end for;
			if verbose gt 0 then fprintf "/dev/stderr","%o:Finished coefficients %o (%o of %o) for number field %o for elliptic curve %o in %.3os\n", jobid, sprint(c), ccnt, #coeff_set, Kstr, Estr, Cputime()-Cstart; end if;
		end for;
		fprintf "/dev/stderr","%o:Finished number field %o for elliptic curve %o testing %o coefficient combinations and generating %o Pryms in %.3os\n", jobid, Kstr, Estr, #coeff_set, Kout, Cputime()-Kstart;
	end for;
	if not single then fprintf "/dev/stderr","%o:Finished elliptic curve %o testing %o number fields of which %o passed, generating %o Pryms in %.3os\n", jobid, Estr, #I, Kcnt, Eout, Cputime()-Estart; end if;
end for;
if assigned EKfp then Flush(EKfp); end if;
exit;
