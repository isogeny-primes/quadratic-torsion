function MySquarefreePart(n)
  return &*[f[1] : f in Factorization(n)];
end function;

function SquareFreeDivisors(n)
  return [sign*d : d in Divisors(MySquarefreePart(n)), sign in [-1,1]];
end function;

function X1_V4_twist_cover(d, d1, d2);
  P4<x,y,v,w,z> := ProjectiveSpace(Rationals(),4);
  f1 := -d1*x*y;
  f2 := d2*(x^2+y^2);
  f3 := d*d1*d2*(x^2 - 2*x*y - y^2);
  D := Curve(P4,[v^2-f1, w^2-f2, z^2-f3]);
  return D;
end function;

function X1_V4_twist_elliptic_curves(d, d1, d2)
  H := 10000;
  //A<x,z> := AffineSpace(Rationals(),2);
  R<x> := PolynomialRing(Rationals());
  y := 1;
  f1 := -d1*x*y;
  f2 := d2*(x^2+y^2);
  f3 := d*d1*d2*(x^2 - 2*x*y - y^2);
  //E1 := ProjectiveClosure(Curve(A,[z^2 -f2*f3]));
  //E2 := ProjectiveClosure(Curve(A,[z^2 -f1*f3]));
  //E3 := ProjectiveClosure(Curve(A,[z^2 -f1*f2]));
  E1 := HyperellipticCurve(f2*f3);
  E2 := HyperellipticCurve(f1*f3);
  E3 := HyperellipticCurve(f1*f2);
  //EE1 := MinimalModel(EllipticCurve(E1,PointSearch(E1,H: OnlyOne:=true)[1]));
  //EE2 := MinimalModel(EllipticCurve(E2,PointSearch(E2,H: OnlyOne:=true)[1]));
  //EE3 := MinimalModel(EllipticCurve(E3,PointSearch(E3,H: OnlyOne:=true)[1]));
  EE1 := MinimalModel(EllipticCurve(E1,Points(E1: Bound:=H)[1]));
  EE2 := MinimalModel(EllipticCurve(E2,Points(E2: Bound:=H)[1]));
  EE3 := MinimalModel(EllipticCurve(E3,Points(E3: Bound:=H)[1]));
  return [EE1, EE2, EE3];
end function;

function LocalPrimesToCheck(D)
  primes := [];
  g := Genus(D);
  for p in PrimesUpTo(200) do
    if (p+1)^2 gt 4*p*g^2 then
      break;
    end if;
    Append(~primes, p);
  end for;
  return primes;
end function;

function IsLocallySolvableGood(D)
  for p in LocalPrimesToCheck(D) do
    if not IsLocallySolvable(D, p) then
      return false;
    end if;
  end for;
  return true;
end function;

function UniqueSort(sequence)
  return Sort(Setseq(Seqset(sequence)));
end function;

function IsLocallySolvableBad(D, badprimes)
  primes := UniqueSort(LocalPrimesToCheck(D) cat badprimes);
  for p in LocalPrimesToCheck(D) do
    if not IsLocallySolvable(D, p) then
      return false, p;
    end if;
  end for;
  return true, 0;
end function;

/*
C := X1_V4_twist_cover(1, 1, 1);
G := AutomorphismGroup(C);
for g in Automorphisms(C) do
  Gi := AutomorphismGroup(C, [G ! g]);
  if #Gi eq 1 then continue; end if;
  Ci := CurveQuotient(Gi);
  if Genus(Ci) gt 1 then
    is_hyperelliptic, CHi := IsHyperelliptic(Ci);
    print Genus(Ci), #AutomorphismGroup(Ci), is_hyperelliptic;
    if is_hyperelliptic then
      print Factorization(HyperellipticPolynomials(CHi));
    else
      print Ci;
    end if;
    if #AutomorphismGroup(Ci) gt 4 then
      C8 := Ci;
    end if;
  else
    print Genus(Ci);
  end if;
end for;
*/
/*
auts := Automorphisms(C);
//for g1 in Automorphisms(C) do
//for g2 in Automorphisms(C) do
for i in [1..#auts] do
for j in [i+1..#auts] do
  g1 := auts[i];
  g2 := auts[j];
  Gi := AutomorphismGroup(C, [G ! g1, G ! g2]);
  if #Gi lt 4 then continue; end if;
  Ci := CurveQuotient(Gi);
  if Genus(Ci) gt 1 then
    print Genus(Ci), #AutomorphismGroup(Ci);
  else
    print Genus(Ci);
  end if;
end for;
end for;
*/

N := 51;
verbose := false;
todo := [];
todo0 := [];
for d1 in SquareFreeDivisors(2*N) do
  for d2 in SquareFreeDivisors(2*N) do
    D := X1_V4_twist_cover(N, d1, d2);
    is_solvable, p :=  IsLocallySolvableBad(D, PrimeDivisors(2*N));
    if is_solvable then
      is_rank0 := false;
      for E in X1_V4_twist_elliptic_curves(N, d1, d2) do
        lb,ub := RankBounds(E);
        if lb eq 0 then
          assert ub eq 0;
          is_rank0 := true;
        end if;
      end for;
      if is_rank0 then
        Append(~todo0, [d1, d2]);
      else
        Append(~todo, [d1, d2]);
      end if;
    end if;
    if verbose then print d1, d2, is_solvable, p; end if;
  end for;
end for;
print todo;
print todo0;

N := 79;
verbose := false;
todo := [];
todo0 := [];
for d1 in SquareFreeDivisors(2*N) do
  for d2 in SquareFreeDivisors(2*N) do
    D := X1_V4_twist_cover(N, d1, d2);
    is_solvable, p :=  IsLocallySolvableBad(D, PrimeDivisors(2*N));
    if is_solvable then
      is_rank0 := false;
      for E in X1_V4_twist_elliptic_curves(N, d1, d2) do
        lb,ub := RankBounds(E);
        if lb eq 0 then
          assert ub eq 0;
          is_rank0 := true;
        end if;
      end for;
      if is_rank0 then
        Append(~todo0, [d1, d2]);
      else
        Append(~todo, [d1, d2]);
      end if;
    end if;
    if verbose then print d1, d2, is_solvable, p; end if;
  end for;
end for;
print todo;
print todo0;



N := 94;
verbose := false;
todo := [];
todo0 := [];
for d1 in SquareFreeDivisors(2*N) do
  for d2 in SquareFreeDivisors(2*N) do
    D := X1_V4_twist_cover(N, d1, d2);
    is_solvable, p :=  IsLocallySolvableBad(D, PrimeDivisors(2*N));
    if is_solvable then
      is_rank0 := false;
      for E in X1_V4_twist_elliptic_curves(N, d1, d2) do
        lb,ub := RankBounds(E);
        if lb eq 0 then
          assert ub eq 0;
          is_rank0 := true;
        end if;
      end for;
      if is_rank0 then
        Append(~todo0, [d1, d2]);
      else
        Append(~todo, [d1, d2]);
      end if;
    end if;
    if verbose then print d1, d2, is_solvable, p; end if;
  end for;
end for;
print todo;
print todo0;