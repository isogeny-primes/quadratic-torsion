///////////////////////////////////////////////////////////////////////
// MWSieve-new.m                                                     //
//                                                                   //
// Mordell-Weil Sieve computation as described in                    //
// N. Bruin, M. Stoll:                                               //
//  The Mordell-Weil Sieve: Proving non-existence of rational points //
//  on curves                                                        //
//                                                                   //
// Version of November 2009                                          //
///////////////////////////////////////////////////////////////////////

// To use this file, do
// Attach("MWSieve-new.m");
//
// The main function is:
/*
intrinsic HasPointMWSieve(J::JacHyp, bas::[JacHypPt], deg3::RngUPolElt
                            : SmoothBound := 200, testfun := func<p, v | IsOdd(v)>,
                              eps := 0.01, eps1 := 0.1, CheckSmall := true)
                           -> BoolElt, PtHyp, SeqEnum, SetEnum, SeqEnum
{Do a Mordell-Weil sieve computation in order to find out if the curve of J
(must be of genus 2, defined over Q and of the form y^2 = f(x)) has any
rational points.
bas is a sequence of generators of the Mordell-Weil group,
deg3 is a polynomial b(x) such that  f(x) - b(x)^2 has a factor of odd degree.
SmoothBound, testfun, eps and eps1 are technical parameters. If CheckSmall
is true, the function searches for small points on the curve first.
The first return value is true or false. If true, the second reeturn value
is a rational point on the curve. Further return values have a more technical
meaning.}
*/
// see at the end of this file.
//
// As an example, consider the following:
/*
Attach("MWSieve-new.m");
SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...
P<x> := PolynomialRing(Rationals());
f := -3*x^6 + x^5 - 3*x^4 + 2*x^3 + 3*x^2 - x + 3;
C := HyperellipticCurve(f);
J := Jacobian(C);
bas := [elt<J | x^2+1, x-1, 2>, elt<J | x^2-x+1, 2*x, 2>,
        elt<J | x^2 + 33868/8917*x + 62637/8917,
                863714233/79512889*x - 557411235/79512889, 2>];
deg3 := -5/4*x^2 - 1/2*x + 1;
HasPointMWSieve(J, bas, deg3);
*/
// (This is one of the rank 3 examples mentioned in the paper.)

/***********************************************************
 disclog.m
 
 General purpose discrete log for groups of smooth order
 
 M. Stoll, started 2005-06-07
 converted to package file 2006-03-05
 ***********************************************************/

declare verbose GroupInfo, 3;
declare verbose MWSieve, 3;

// given: Abelian group G, bijective map G -> X, X some structure
// #G smooth (so that for groups of order p^f|#G, lookup is feasible)

// Exported intrinsics: 
//  MakeDL(G, m, mul, sub)
//     m : G -> X  is the map (UserProgram)
//   mul : Z x X -> X  is multiplication by integers (UserProgram)
//   sub : X x X -> X  is subtraction (UserProgram)
// MakeDL(G, m)
//     m : G -> X is the map (Map), * and + defined on X

function MakeLookup(G, m, extract)
  pairs := [<extract(m(g)), g> : g in G];
  ass := pmap<{p[1] : p in pairs} -> G| pairs>;
  return func<x | ass(extract(x))>;
end function;

function MakeDLp(G, m, p, mul, sub, extract)
  // G a p-group
  // mul = scalar multplication in image group
  // sub = subtraction
  if #G le 25 then
    return MakeLookup(G, m, extract);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup(G, m, extract);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  f1 := MakeLookup(G1, func<x | m(G!x)>, extract);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  f2 := MakeDLp(G2, func<x | m(G!x)>, p, mul, sub, extract);
  return func<x | f2(sub(x, m(G!a))) + a where a := f1(mul(pp,x)) @@ h>;
end function;

intrinsic MakeDL(G::GrpAb, m::UserProgram, mul::UserProgram, sub::UserProgram
                  : extract := func<x | x>) -> UserProgram
{ Given bijection  m : G -> X, multiplication by integers on X, subtraction 
  on X, compute the inverse of m. Assumes that #G is smooth.}
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    DLp := MakeDLp(Gp, func<x | m(G!x)>, p, mul, sub, extract);
    Append(~DLs, DLp);
  end for;
  return func<x | &+[G|refs[i]*G!(DLs[i](mul(cofs[i],x))) : i in [1..#f]]>;
end intrinsic;

function MakeLookup1(G, m)
  return pmap<Codomain(m) -> G| [<m(g), g> : g in G]>;
end function;

function MakeDLp1(G, m, p)
  // G a p-group
  if #G le 25 then
    return MakeLookup1(G, m);
  end if;
  invs := Invariants(G);
  // printf "MakeDLp: Invariants(G) = %o\n", invs;
  pp := ExactQuotient(invs[#invs], p);
  if pp eq 1 then
    return MakeLookup1(G, m);
  end if;
  // printf "MakeDLp: pp = %o\n", pp;
  h := hom<G -> G | [pp*G.i : i in [1..#invs]]>;
  G1 := Image(h);
  // printf "MakeDLp: Invariants(Image(h)) = %o\n", Invariants(G1);
  m1 := map<G1 -> Codomain(m) | x:->m(x)>;
  f1 := MakeLookup1(G1, m1);
  G2 := Kernel(h);
  // printf "MakeDLp: Invariants(Kernel(h)) = %o\n", Invariants(G2);
  m2 := map<G2 -> Codomain(m) | x:->m(x)>;
  f2 := MakeDLp1(G2, m2, p);
  return pmap<Codomain(m) -> G |
               x :-> f2(x - m(a)) + a where a := f1(pp*x) @@ h>;
end function;

intrinsic MakeDL(G::GrpAb, m::Map) -> Map
{ Given bijection  m : G -> X, where X has group structure, compute the
  inverse of m. Assumes that #G is smooth.}
  n := #Invariants(G);
  f := Factorization(#G);
  cofs := [&*[Integers()|f[i,1]^f[i,2] : i in [1..#f] | i ne j] : j in [1..#f]];
  _, refs := XGCD(cofs);
  assert &+[Integers()|refs[i]*cofs[i] : i in [1..#f]] eq 1;
  DLs := [**];
  for i := 1 to #f do
    p := f[i,1];
    hp := hom<G -> G | [cofs[i]*G.j : j in [1..n]]>;
    Gp := Image(hp);
    mp := map<Gp -> Codomain(m) | x:->m(x)>;
    DLp := MakeDLp1(Gp, mp, p);
    Append(~DLs, DLp);
  end for;
  return pmap<Codomain(m) -> G
               | x :-> &+[G|refs[i]*G!(DLs[i](cofs[i]*x)) : i in [1..#f]]>;
end intrinsic;

//////////////////////////////////////////////////////////////////////////

/*********************************************************************
 * g2-jacobian-equations.m
 *
 * smooth projective model of genus 2 Jacobian in P^15
 *
 * M. Stoll, started 2006-03-05
 *
 * 2008-10-10: replaced equations coming from Victor Flynn's ftp file
 *  by slightly changed ones that also work in characteristic 2
 *
 * Also: JPttoCoords(f,a,b,d), works in arbitrary charcateristic!
 *********************************************************************/

intrinsic JacEquations(fpol::RngUPolElt) -> SeqEnum
{ Given polynomial f, return the 72 quadrics defining the Jacobian of
  y^2 = f(x) in P^15. }
  R := Universe(Coefficients(fpol));
  require Degree(fpol) le 6: "The polynomial must be of degree at most 6.";
  P16<[z]> := PolynomialRing(R, 16);
  a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15 := Explode(z);
  f0,f1,f2,f3,f4,f5,f6 := Explode([Coefficient(fpol, i) : i in [0..6]]);
  eqns := [
     // 1
     -a0*a11 + a2*a6 + a3*a4 + f5*a3*a10 + f1*a3*a14 + f1*a4*a13 - f2*a5*a11 -
        5*f1*a5*a12 - 2*f0*a5*a13 - f1*a5*a15 + f1*f4*a10*a14 - 2*f0*f4*a11*a14
        + (-3*f0*f5 - 2*f1*f4)*a12^2 - 5*f0*f3*a12*a14 - f0*f5*a12*a15 +
        (-2*f0*f2 + f1^2)*a13*a14 - f0*f3*a14*a15,
       // replaces -a0*a11+f1*a14*a3+f3*a10*a5+f5*a3*a10+2*a4*a3,
     // 2
     -a0*a10+a3^2,
     // 3
     -a0*a12+a3*a5,
     // 4
     -f0*f2*a14^2-f0*a14*a5-8*f0*f6*a12^2-f3*f5*a12*a10-f1*f6*a13*a10
       -f2*f5*a13*a10-f1*f5*a13*a11-3*f5*f0*a13*a12-f1*f3*a14*a12
       -f3*f0*a14*a13-f0*f6*a14*a10-f2*f4*a14*a10+a4^2-a0*a12-6*f0*f6*a12*a15
       -f2*f6*a10*a15-f1*f6*a11*a15-f5*f0*a13*a15-f1*f4*a14*a11-f2*a12*a5
       -f4*f0*a13^2-f0*f6*a15^2-f4*f6*a10^2-f6*a10*a3-f4*a10*a5-f3*f6*a10*a11
       -4*f2*f6*a10*a12-2*f1*f6*a11*a12,
     // 5
     -a0*a13 + a2*a8 - f6*a3*a11 + f3*a3*a14 + a4*a5 + f1*a5*a14 + f3*f5*a10*a13
        - f3*f5*a11*a12 + 2*f0*f6*a11*a14 + 4*f1*f6*a12^2 + (4*f0*f6 +
        f1*f5)*a12*a13 + (7*f0*f5 + f1*f4)*a12*a14 + f1*f6*a12*a15 +
        2*f0*f4*a13*a14 + 2*f0*f6*a13*a15 + f0*f3*a14^2 + 2*f0*f5*a14*a15,
       // replaces -a0*a13+f1*a14*a5+f3*a14*a3+f5*a10*a5+2*a5*a4,
     // 6
     -a0*a14+a5^2,
     // 7
     -4*f0*f2*a14^2-4*f0*a14*a5+a0*a15-36*f0*f6*a12^2-4*f3*f5*a12*a10
       -4*f1*f6*a13*a10-4*f2*f5*a13*a10-12*f5*f0*a13*a12-2*f1*f3*a14*a12
       -4*f3*f0*a14*a13-4*f2*f4*a14*a10-4*f5*a10*a4-f5^2*a10^2-24*f0*f6*a12*a15
       -4*f2*f6*a10*a15-4*f1*f6*a11*a15-4*f5*f0*a13*a15-4*f1*f4*a14*a11
       +f3^2*a14*a10-2*f3*a11*a5-16*f1*f5*a12^2-2*f1*a13*a5-4*f2*a12*a5
       -4*f0*f6*a15^2-4*f4*f6*a10^2-4*f6*a10*a3-4*f4*a10*a5-4*f3*f6*a10*a11
       -16*f2*f6*a10*a12-8*f1*f6*a11*a12+f1^2*a14^2-16*f0*f4*a14*a12
       -4*f1*f5*a12*a15-4*f0*f4*a14*a15,
     // 8
     -f1*a14^2-f3*a14*a12+2*f4*a13*a12-f5*a12^2-2*a4*a14-2*f4*a14*a11+a5*a13,
     // 9
     -f1*a14*a12-f3*a14*a10-f5*a12*a10-2*a4*a12+a5*a11,
     // 10
     2*f4*a14*a10+2*f5*a12*a11-4*a5*a12-2*f4*a12^2-a5*a15+f1*a14*a13
       +f3*a14*a11-f5*a13*a10+2*a4*a13,
     // 11
     -f5*a10^2-f3*a10*a12+2*f2*a11*a12-f1*a12^2-2*a4*a10-2*f2*a13*a10+a3*a11,
     // 12
     f2*a12^2+f1*a13*a12-a5*a10-f1*a14*a11-f2*a10*a14+a3*a12,
     // 13
     f5*a13*a10+f4*a14*a10-a5*a12-f4*a12^2-f5*a12*a11+a3*a14,
     // 14
     -f1*a14*a12-f3*a14*a10-f5*a12*a10-2*a4*a12+a3*a13,
     // 15
     4*f1*a13*a12-2*a5*a10-3*f1*a14*a11-a3*a15-2*a3*a12+f5*a10*a11
       +f3*a10*a13+2*a4*a11,
     // 16
     -a14*a15-4*a12*a14+a13^2,
     // 17
     -a10*a14+a12^2,
     // 18
     -a10*a15-4*a10*a12+a11^2,
     // 19
     -a11*a13 + 4*a12^2 + a12*a15,
       // replaces -a11*a13+2*a10*a14+a12*a15+2*a12^2,
     // 20
     -a12*a13+a11*a14,
     // 21
     -a11*a12+a10*a13,
     // 22
     -a10^2*f2*f5^2-a11^2*f0*f5^2+a1^2-a0*a3+8*f0*f6*a4*a11-a10^2*f3^2*f6
       -f4*a3^2-f0*a5^2+4*a10^2*f1*f5*f6+4*a10^2*f2*f4*f6-a10*a3*f3*f5
       +4*a10*a3*f2*f6+8*f1*f6*a10*a4+f1*f5*a10*a5+4*a11^2*f0*f4*f6
       -a10*a11*f1*f5^2+4*a10*a11*f0*f5*f6+4*a10*a11*f1*f4*f6+4*f0*f5*a12*a4
       +2*a12*a10*f0*f5^2+6*a12*a10*f1*f3*f6+8*f0*f3*f6*a12*a11
       +4*a14*a10*f0*f2*f6+2*a14*a10*f0*f3*f5+3*a14*a10*f1^2*f6
       +4*f0*f1*f6*a14*a11+2*f0*f1*f5*a14*a12,
     // 23
     a1*a2-a0*a4+3*a13*a10*f0*f5^2+a13*a10*f1*f3*f6+2*a10^2*f2*f5*f6
       +f3*f6*a10*a3+4*f2*f6*a10*a4+a10*a5*f2*f5+5*a10*a5*f1*f6+4*f1*f6*a12*a3
       +20*f0*f6*a12*a4+10*f0*f5*f6*a10*a12+2*a12^2*f1*f3*f5+28*a12^2*f0*f3*f6
       +4*a12^2*f1*f2*f6+3*f1*f5*a12*a4+2*a12*a10*f1*f4*f6+2*a12*a10*f2*f3*f6
       +a12*a10*f1*f5^2-4*f0*f5^2*a12*a11-4*f0*f6*f4*a12*a11+2*f0*f4*a13*a5
       +8*a10*a13*f0*f4*f6+8*a13*a12*f0*f2*f6+3*a13*a12*f0*f3*f5
       -a13*a12*f1^2*f6+9*a14*a3*f0*f5+a14*a3*f1*f4+f0*f3*a14*a5
       -2*f1*f6*f2*a14*a10-8*f0*f6*f3*a14*a10-2*f0*f5*f3*a14*a11
       -4*f0*f6*f2*a14*a11+10*f1*f6*f0*a14*a12+2*a14*a12*f0*f2*f5
       +a14*a12*f1^2*f5+2*f1*f6*a3*a15+4*f0*f6*a4*a15+2*f0*f5*a5*a15
       +2*f0*f5*f6*a10*a15+4*f0*f3*f6*a12*a15+2*f1*f6*f0*a14*a15,
     // 24
     -a14^2*f0*f3^2-a14^2*f1^2*f4+a2^2-a0*a5-f6*a3^2-f2*a5^2+8*a13*a4*f0*f6
       +4*f0*f5*a13*a5+4*a13*a10*f0*f5*f6-4*a13*a10*f1*f4*f6+4*f0*f4*a14*a5
       +4*a10*a14*f0*f4*f6-a10*a14*f0*f5^2+4*a10*a14*f1*f3*f6+8*f1*f6*a12*a4
       +4*f1*f5*f6*a12*a10+4*f1*f6*f4*a12*a11-2*f1*f6*a13*a3+4*a14*a13*f0*f1*f6
       +4*a14*a13*f0*f2*f5-a14*a13*f1^2*f5+4*a14^2*f0*f2*f4+f1*f5*a14*a3
       -a14*a5*f1*f3+8*a14*a11*f0*f3*f6+16*a14*a12*f0*f2*f6+2*a14*a12*f0*f3*f5
       +4*a14*f0*f2*f6*a15-a14*f1^2*f6*a15,
     // 25
     -a0*a14-f2*a14*a5-f3*a14*a4-2*f4*a14*a3-3*f5*a4*a12-f6*a3*a15
       -5*f6*a3*a12-f1*f3*a14^2-f1*f4*a14*a13-f1*f5*a14*a15-5*f1*f5*a12*a14
       -f1*f6*a13*a15-3*f1*f6*a13*a12-2*f2*f4*a14*a12-2*f2*f5*a13*a12
       -2*f2*f6*a13*a11-3*f3*f5*a14*a10-2*f3*f6*a12*a11-2*f4*f6*a12*a10
       -f5^2*a12*a10+a2*a9,
     // 26
     -a0*a13+f1*a14*a5+f3*a5*a12-f5*a10*a5-2*f6*a11*a3+2*f0*f3*a14^2
       +4*f0*f4*a14*a13+4*f5*f0*a14*a15+14*f5*f0*a14*a12+4*f0*f6*a13*a15
       +8*f0*f6*a13*a12+4*f0*f6*a14*a11+2*f1*f4*a14*a12+2*f1*f5*a13*a12
       +2*f1*f6*a12*a15+8*f1*f6*a12^2+2*a2*a8,
     // 27
     -a0*a12 + a2*a7 - f6*a3*a10 + f2*a3*a14 + 2*f3*a4*a12 - f1*a4*a14 -
       f3*a5*a11 - 2*f2*a5*a12 - 2*f0*a5*a14 + (-8*f2*f6 + f3*f5)*a10*a12 -
       2*f1*f6*a10*a13 + (4*f0*f6 + f3^2)*a10*a14 - 2*f2*f6*a10*a15 +
       2*f2*f6*a11^2 + 3*f1*f6*a11*a12 + (3*f0*f5 - f1*f4)*a11*a14 +
       2*f0*f6*a12^2 + (-2*f0*f5 + f1*f4)*a12*a13 + 2*f0*f6*a12*a15 -
       f0*f3*a13*a14 - 2*f0*f2*a14^2,
       // replaces
       //  2*f2*a3*a14-a0*a15+40*f0*f6*a12^2+6*f3*f5*a12*a10+4*f2*f5*a13*a10
       // +8*f5*f0*a13*a12+3*f1*f3*a14*a12+2*f3*f0*a14*a13+8*f0*f6*a14*a10
       // +4*f2*f4*a14*a10-2*a0*a12+4*f5*a10*a4+f5^2*a10^2+4*f3*a12*a4
       // +28*f0*f6*a12*a15+4*f1*f6*a11*a15+4*f5*f0*a13*a15+4*f1*f4*a14*a11
       // +f3^2*a14*a10+4*f2*f6*a11^2+16*f1*f5*a12^2+f1*a13*a5+2*a2*a7
       // +4*f0*f6*a15^2+4*f4*f6*a10^2+2*f6*a10*a3+4*f4*a10*a5+4*f3*f6*a10*a11
       // +14*f1*f6*a11*a12+16*f0*f4*a14*a12+4*f1*f5*a12*a15+4*f0*f4*a14*a15
       // +f1*f5*a14*a10+6*a14*a11*f0*f5,
     // 28
     -a0*a11-4*f0*a13*a5-f1*a15*a5-5*f1*a12*a5-2*f2*a11*a5-f3*a10*a5
       +f5*a3*a10-4*f0*f2*a14*a13-2*f3*f0*a15*a14-10*f0*f3*a14*a12
       -4*f0*f4*a14*a11-2*a15*a12*f0*f5-6*f0*f5*a12^2+f1^2*a14*a13
       -f1*f3*a14*a11-2*f1*f4*a12^2-f1*f5*a13*a10+2*a2*a6,
     // 29
     -a0*a10-f4*a3*a10-f3*a4*a10-2*f2*a10*a5-3*f1*a12*a4-f0*a15*a5
       -5*f0*a12*a5-f5*f3*a10^2-f5*f2*a10*a11-f1*f5*a15*a10-5*f1*f5*a10*a12
       -a15*a11*f0*f5-3*f5*f0*a11*a12-2*f4*f2*a10*a12-2*f4*f1*a11*a12
       -2*f0*f4*a13*a11-3*a14*a10*f1*f3-2*f3*f0*a13*a12-2*f0*f2*a14*a12
       -f1^2*a14*a12+a6*a1,
     // 30
     a1*a7 - a3*a4 + f3*a3*a12 - f1*a3*a14 - f3*a5*a10 - f0*a5*a13 + f3*f6*a10^2
        + 2*f2*f6*a10*a11 + (7*f1*f6 + f2*f5)*a10*a12 + 2*f0*f6*a10*a13 -
        f2*f3*a10*a14 + 2*f1*f6*a10*a15 + (4*f0*f6 + f1*f5)*a11*a12 +
        2*f0*f6*a11*a15 + (4*f0*f5 + f2*f3)*a12^2 + f0*f5*a12*a15,
       // replaces
       // -a0*a11+f5*a3*a10+f3*a3*a12-f1*a14*a3-2*f0*a13*a5+2*f6*f3*a10^2
       //   +4*f2*f6*a10*a11+4*a10*f1*f6*a15+14*a10*a12*f1*f6+4*f0*f6*a15*a11
       //   +8*f0*f6*a12*a11+4*f0*f6*a13*a10+2*f2*f5*a12*a10+2*f1*f5*a12*a11
       //   +2*a15*a12*f0*f5+8*f0*f5*a12^2+2*a1*a7,
     // 31
     a1*a8 - a2*a7 - f6*a3*a10 + f5*a3*a11 - f2*a3*a14 - 3*f5*a4*a10 +
        3*f1*a4*a14 - f4*a5*a10 + 2*f2*a5*a12 - f1*a5*a13 + f0*a5*a14 +
        (-2*f4*f6 - f5^2)*a10^2 - f3*f6*a10*a11 + (8*f2*f6 - 2*f3*f5)*a10*a12 +
        (3*f1*f6 - 3*f2*f5 - f3*f4)*a10*a13 - 2*f2*f4*a10*a14 + 2*f2*f6*a10*a15
        - 2*f2*f6*a11^2 + (-3*f1*f6 + 3*f2*f5 + f3*f4)*a11*a12 + (-3*f0*f5 +
        f1*f4 + f2*f3)*a11*a14 + 2*f2*f4*a12^2 + (3*f0*f5 - f1*f4 -
        f2*f3)*a12*a13 + (-8*f0*f4 + 2*f1*f3)*a12*a14 + 2*f0*f4*a13^2 +
        f0*f3*a13*a14 + (2*f0*f2 + f1^2)*a14^2 - 2*f0*f4*a14*a15,
       // replaces
       // 4*f0*f2*a14^2+2*f0*a14*a5+f5*a3*a11-a0*a15+40*f0*f6*a12^2
       //   +3*f3*f5*a12*a10+6*f1*f6*a13*a10+14*f5*f0*a13*a12+6*f1*f3*a14*a12
       //   +4*f3*f0*a14*a13+8*f0*f6*a14*a10-2*a0*a12+4*f3*a12*a4+28*f0*f6*a12*a15
       //   +4*f2*f6*a10*a15+4*f1*f6*a11*a15+4*f5*f0*a13*a15+4*f1*f4*a14*a11
       //   +f3^2*a14*a10+2*a1*a8+16*f1*f5*a12^2+4*f2*a12*a5+4*f4*f0*a13^2
       //   +4*f0*f6*a15^2+2*f4*a10*a5+2*f3*f6*a10*a11+16*f2*f6*a10*a12
       //   +8*f1*f6*a11*a12+f1^2*a14^2+4*f1*f5*a12*a15+f1*f5*a14*a10
       //   +4*f2*f4*a12^2+4*f1*a14*a4+2*a12*a11*f3*f4+4*f2*f5*a12*a11
       //   -2*a10*a13*f3*f4-2*a13*a12*f2*f3+2*a14*a11*f2*f3,
     // 32
     a1*a9 - 2*f6*a3*a11 - 3*f5*a3*a12 - f4*a3*a13 - f3*a3*a14 - f5*a3*a15 -
        a4*a5 + f5*a4*a11 - 2*f5*a5*a10 + (-2*f4*f6 + f5^2)*a10*a11 -
        5*f3*f6*a10*a12 - 2*f2*f6*a10*a13 - f2*f5*a10*a14 - f3*f6*a10*a15 -
        2*f1*f5*a11*a14 - 3*f1*f6*a12^2 + 2*f1*f5*a12*a13 - f1*f6*a12*a15,
       // replaces
       // -a0*a13-4*f6*a11*a3-f5*a3*a15-5*f5*a3*a12-2*f4*a13*a3-f3*a14*a3
       //   +f1*a14*a5-4*f6*f4*a10*a11-2*f6*f3*a10*a15-10*f6*f3*a10*a12
       //   -4*f2*f6*a13*a10-2*f1*f6*a12*a15-6*f1*f6*a12^2+f5^2*a10*a11
       //   -f3*f5*a13*a10-2*f5*f2*a12^2-f1*f5*a14*a11+2*a1*a9,
     // 33
     -a5*a14-f2*a14^2-f3*a14*a13-f4*a13^2-3*f5*a13*a12-f5*a13*a15
       -f6*a14*a10-6*f6*a12*a15-8*f6*a12^2-f6*a15^2+a9^2,
     // 34
     a9*a8-a4*a14-f3*a14*a12-f4*a14*a11-f5*a12*a15-4*f5*a12^2-f6*a11*a15
       -2*f6*a11*a12-f6*a13*a10,
     // 35
     a9*a7+a5*a12+f2*a14*a12-f6*a15*a10-3*f6*a10*a12-f4*a14*a10-f5*a12*a11
       +f4*a12^2-a4*a13,
       // replaces
       // 2*a9*a7-a5*a15-2*a5*a12+f1*a14*a13+2*f2*a14*a12+f3*a14*a11
       //  -f5*a13*a10-2*f6*a15*a10-6*f6*a10*a12 //
      //  - 2*f4*a14*a10-2*f5*a12*a11+4*a5*a12+2*f4*a12^2+a5*a15-f1*a14*a13
      //     -f3*a14*a11+f5*a13*a10-2*a4*a13,
     // 36
     a6*a9-a4*a15-a4*a12+f2*a14*a11+2*f3*a14*a10+f4*a12*a11+f1*a14*a12
       +f5*a12*a10,
     // 37
     a8^2-a5*a12-f0*a14^2-f4*a12^2-f5*a12*a11-f6*a15*a10-4*f6*a10*a12,
     // 38
     a7*a8-a4*a12-f0*a14*a13-f1*a14*a12-f5*a12*a10-f6*a10*a11,
     // 39
     a6*a8-a3*a12+f4*a12*a10+f1*a14*a11-f0*a15*a14-3*f0*a14*a12
       -2*f1*a13*a12+a5*a10+a3*a12-a4*a11,
       // replaces
       // 2*a6*a8-a3*a15-2*a3*a12+f5*a10*a11+2*f4*a12*a10+f3*a10*a13
       //  -f1*a14*a11-2*f0*a15*a14-6*f0*a14*a12
     // 40
     a7^2-a5*a10-f0*a15*a14-4*f0*a14*a12-f1*a14*a11-f2*a10*a14-f6*a10^2,
     // 41
     a6*a7-a4*a10-f3*a10*a12-f2*a13*a10-f1*a12*a15-4*f1*a12^2-f0*a15*a13
       -2*f0*a13*a12-f0*a11*a14,
     // 42
     -a3*a10-f4*a10^2-f3*a11*a10-f2*a11^2-3*f1*a11*a12-f1*a15*a11
       -f0*a14*a10-6*f0*a15*a12-8*f0*a12^2-f0*a15^2+a6^2,
     // 43
     -f1*a9*a3+a14*a8*f1^2+4*f1*a8*a4+2*f3*a3*a7+a3*a1-f3*a2*a10
       +4*f0*a8*a5-a6*a0+2*f2*a8*a3-2*f0*f5*a10*a9+3*f1*f5*a10*a8
       +2*f1*f6*a11*a6+12*f0*f5*a12*a7+12*f0*f6*a12*a6+4*a12*a8*f0*f4
       +2*a12*a8*f1*f3+2*a12*a7*f1*f4+2*a12*a6*f1*f5+4*a14*a8*f0*f2
       +4*f0*f3*a14*a7+4*f0*f4*a14*a6+4*f0*f5*a7*a15+4*f0*f6*a6*a15,
     // 44
     -a7*a0+2*f0*a9*a5+f1*a8*a5+a2*a3,
     // 45
     f5*a10*a2+a2*a4+a14*a8*f2^2-a0*a8+f6*a6*a3-f2*a9*a4-f2*f4*a11*a9
       +a11*a8*f1*f6-a11*a8*f2*f5+4*f2*f4*a12*a8+4*a12*a7*f2*f5
       -4*a12*a7*f1*f6+3*f2*f6*a12*a6+f0*f5*a12*a9-f0*f3*a14*a9
       -a14*a8*f1*f3+a14*a7*f2*f3-a14*a7*f1*f4-f1*f5*a14*a6+f2*f4*a8*a15
       +a7*f2*f5*a15-a7*f1*f6*a15+f2*f6*a6*a15,
     // 46
     -f3^2*a14*a7-2*a10*a7*f5^2+4*f6*a7*a3+a2*a5+4*f1*f6*a11*a9-a0*a9
       +f3*a9*a4+3*f5*a3*a8+2*f4*a7*a5+4*f0*f5*a13*a9-2*f5*f6*a10*a6
       +4*a10*a7*f4*f6+4*f3*f6*a10*a8+4*f2*f6*a10*a9+12*f0*f6*a12*a9
       -f3*f6*a12*a6+4*a12*a8*f2*f5+4*a12*a9*f1*f5+4*a12*a7*f2*f6
       +2*a12*a7*f3*f5-a12*a8*f3*f4-f3*f5*a13*a6+2*f1*f5*a14*a7
       -a14*a6*f3*f4-a14*a8*f2*f3+2*a14*a6*f1*f6+4*f0*f6*a9*a15-f3*f6*a6*a15,
     // 47
     -a0*a8+2*f6*a6*a3+f5*a3*a7+a5*a1,
     // 48
     f0*a9*a5+a1*a4-f4*f2*a13*a6+a10*a7*f4^2+f1*a14*a1-f4*a6*a4
       +f6*f1*a12*a6-a7*a0+a13*a7*f0*f5-a13*a7*f1*f4-f6*f3*a10*a6
       -a10*a7*f3*f5+a10*a8*f3*f4-a10*a8*f2*f5-f5*f1*a10*a9
       +4*f2*f4*a12*a7+4*a12*a8*f1*f4-4*f0*f5*a12*a8+3*f4*f0*a12*a9
       +f2*f4*a7*a15+a8*f1*f4*a15-f0*f5*a8*a15+f4*f0*a9*a15,
     // 49
     -a9*a5+f3*a14*a8+2*f4*a14*a7+2*f5*a14*a6+2*f6*a13*a6+f5*a8*a12+a2*a14,
     // 50
     -2*a5*a8-f1*a14*a9-2*f2*a14*a8-f3*a14*a7+f5*a7*a12+2*f6*a12*a6+a2*a13,
     // 51
     -a5*a7+2*f0*a14*a9+f1*a14*a8+a2*a12,
     // 52
     -a3*a7+2*f0*a12*a9+f1*a12*a8+a2*a10,
     // 53
     -2*a8*a3-f1*a12*a9-2*f2*a12*a8-f3*a12*a7+f5*a10*a7+2*f6*a10*a6+a2*a11,
     // 54
     -2*a5*a7-f1*a13*a9-2*f2*a14*a7-2*f2*a12*a9-f3*a14*a6-3*f3*a8*a12
       -4*f4*a12*a7-3*f5*a12*a6-f5*a10*a8-2*f6*a11*a6+a2*a15+2*a2*a12,
     // 55
     -a3*a6+f3*a10*a7+2*f2*a10*a8+2*f1*a10*a9+2*f0*a11*a9+f1*a12*a7+a1*a10,
     // 56
     -2*a3*a7-f5*a10*a6-2*f4*a10*a7-f3*a10*a8+f1*a12*a8+2*f0*a12*a9+a1*a11,
     // 57
     -a8*a3+2*f6*a10*a6+f5*a10*a7+a1*a12,
     // 58
     -a5*a8+2*f6*a12*a6+f5*a7*a12+a1*a14,
     // 59
     -2*a5*a7-f5*a12*a6-2*f4*a12*a7-f3*a8*a12+f1*a14*a8+2*f0*a14*a9+a1*a13,
     // 60
     -2*a8*a3-f5*a11*a6-2*f4*a8*a10-2*f4*a12*a6-f3*a10*a9-3*f3*a12*a7
       -4*f2*a12*a8-3*f1*a12*a9-f1*a14*a7-2*f0*a13*a9+a1*a15+2*a1*a12,
     // 61
     -a9*a4+f2*a14*a8+f3*a14*a7+f4*a14*a6+f4*a12*a8+f5*a13*a6+f6*a6*a15
       +3*f6*a12*a6+a5*a8,
     // 62
     -a4*a8-f0*a14*a9-f1*a14*a8+f4*a12*a7+f5*a12*a6+f6*a11*a6+a5*a7,
     // 63
     -a4*a7-f0*a13*a9-f1*a14*a7-f1*a12*a9-f2*a12*a8-f3*a12*a7+f6*a10*a6+a6*a5,
     // 64
     -a4*a6+f4*a10*a7+f3*a10*a8+f2*a10*a9+f2*a7*a12+f1*a11*a9+f0*a15*a9
       +3*f0*a12*a9+a3*a7,
     // 65
     -a4*a7-f6*a10*a6-f5*a10*a7+f2*a12*a8+f1*a12*a9+f0*a13*a9+a8*a3,
     // 66
     -a4*a8-f6*a11*a6-f5*a10*a8-f5*a12*a6-f4*a12*a7-f3*a8*a12+f0*a14*a9+a9*a3,
     // 67
     -4*a7*a12-a7*a15+a8*a11+a6*a13,
     // 68
     -4*a8*a12-a8*a15+a7*a13+a9*a11,
     // 69
     -a8*a13+a7*a14+a9*a12,
     // 70
     -a7*a13+a6*a14+a8*a12,
     // 71
     -a8*a11+a9*a10+a7*a12,
     // 72
     -a7*a11+a8*a10+a6*a12];
  return eqns;
end intrinsic;

intrinsic JacEquations(J::JacHyp) -> SeqEnum
{ Return the 72 quadrics defining the model of J in P^15.}
  C := Curve(J);
  require Genus(C) eq 2: "J must be the Jacobian of a genus 2 curve.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of J must be of the form y^2 = f(x).";
  return JacEquations(f);
end intrinsic;

intrinsic JPttoCoords(pt::JacHypPt) -> SeqEnum
{ Given a point on the genus 2 Jacobian J, return the sequence of coordinates
  of its image on the model of J in P^15.}
  J := Parent(pt);
  C := Curve(J);
  require Genus(C) eq 2: "pt must be on the Jacobian of a genus 2 curve.";
  R := BaseField(C);
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of pt must be of the form y^2 = f(x).";
  return JPttoCoords(f, pt[1], pt[2], pt[3]);
end intrinsic;

intrinsic JPttoCoords(f::RngUPolElt, a::RngUPolElt, b::RngUPolElt, d::RngIntElt) -> SeqEnum
{}
  R := Parent(f);
  require Parent(a) cmpeq R and Parent(b) cmpeq R: "Polynomials must be in same ring.";
  require LeadingCoefficient(a) eq 1: "a must be monic.";
  f2,f3,f4,f5,f6 := Explode([Coefficient(f, i) : i in [2..6]]);
  if Degree(a) eq 2 then
    al1 := -Coefficient(a, 1); al2 := Coefficient(a, 0);
    b1 := Coefficient(b, 1); b2 := Coefficient(b, 0);
    a15 := al1^2 - 4*al2;
    a14 := 1;
    a13 := al1;
    a12 := al2;
    a11 := al1*al2;
    a10 := al2^2;
    a9 := b1;
    a8 := -b2;
    a7 := -(al2*b1 + al1*b2);
    a6 := al1*a7 + al2*b2;
    c := al1^2 - al2;
    a5 := b1^2 - (f6*c^2 + f5*al1*c + f4*al1^2 + f3*al1 + f2);
    a4 := -(b1*b2 + f6*al1*al2*c + f5*al1^2*al2 + f4*al1*al2 + f3*al2);
    a3 := al2*a5;
    a2 := a5*a9 - f3*a8 - 2*f4*a7 - 2*f5*a6 - 2*f6*a6*al1 - f5*a8*al2;
    a1 := a5*a8 - 2*f6*a6*al2 - f5*a7*al2;
    a0 := a5^2;
  elif Degree(a) eq 1 then
    s := Coefficient(b, 3);
    assert s^2 eq f6;
    u := -Coefficient(a, 0);
    v := Evaluate(b, u);
    a15 := 1; a14 := 0; a13 := 0; a12 := 0;
    a11 := u; a10 := u^2; a9 := s; a8 := s*u;
    a7 := s*u^2; a6 := s*u^3 - v; a5 := 0; a4 := s*a6;
    t := 2*s*a6 + f5*u^2;
    a3 := t*u; a2 := s*a3; 
    a1 := a7*(4*f6*u^3 + 3*f5*u^2 + 2*f4*u + f3) - u*v*(4*f6*u + f5);
    a0 := t^2;
  elif d eq 2 then // and Degree(a) eq 0
    s := Coefficient(b, 3);
    t := Coefficient(b, 2);
    assert s^2 eq f6;
    assert 2*s*t eq f5;
    a15 := 0; a14 := 0; a13 := 0; a12 := 0;
    a11 := 0; a10 := 1; a9 := 0; a8 := 0;
    a7 := s; a6 := -t; a5 := 0; a4 := s*a6;
    a3 := a6^2 - f4; a2 := s*a3; a1 := a3*a6 - s*f3; a0 := a3^2;
  else // origin
    return [BaseRing(R) | 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  end if;
  return [BaseRing(R) | a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15];
end intrinsic;

function NormSeq(seq)
  l := LCM([Denominator(s) : s in seq]);
  seq := [Numerator(s)*ExactQuotient(l, Denominator(s)) : s in seq];
  g := GCD(seq);
  return [ExactQuotient(s, g) : s in seq];
end function;

intrinsic JPtToCoordsModN(pt::JacHypPt, n::RngIntElt) -> SeqEnum
{ Given a point pt on a genus 2 Jacobian over Q, return its image mod n
  on the model of the Jacobian in P^15.}
  s := ChangeUniverse(NormSeq(JPttoCoords(pt)), Integers(n));
  i := 1; while not IsInvertible(s[i]) do i +:= 1; end while;
  return [a/s[i] : a in s];
end intrinsic;

intrinsic JPtIsNonSingularModP(pt::JacHypPt, p::RngIntElt : Eqns := []) -> BoolElt
{ Given a point pt on a genus 2 Jacobian over Q, check whether its image
  modulo the prime p is nonsingular. The parameter Eqns can be used to 
  specify the equations of the model of the Jacobian in P^15.}
  if IsEmpty(Eqns) then
    C := Curve(Parent(pt));
    require Genus(C) eq 2: "pt must be on the Jacobian of a genus 2 curve.";
    f, h := HyperellipticPolynomials(C);
    require h eq 0: "The curve of pt must be of the form y^2 = f(x).";
    Eqns := JacEquations(PolynomialRing(GF(p))!f);
  end if;
  coords := ChangeUniverse(JPtToCoordsModN(pt, p), GF(p));
  i := 1;
  while coords[i] eq 0 do i +:= 1; end while;
  // affine patch given by ith coordinate = 1
  jmat := Matrix([[Evaluate(Derivative(e, j), coords) : j in [1..16] | j ne i]
                    : e in Eqns]);
  return Rank(jmat) eq 13;
end intrinsic;

//////////////////////////////////////////////////////////////////////////

/*************************************************************************
 * jac-arith.magma
 *
 * Generalized arithmetic on Jacobian schemes (genus 2)
 *
 * M. Stoll, 2008-11-03, initially copied from groupinfo-new.m
 *************************************************************************/

// Test if curve is regular at p (p odd for now)
function IsRegularAtp(C, p)
  // need equation to be (p-)integral
  f, h := HyperellipticPolynomials(C);
  assert h eq 0;
  assert forall{c : c in Coefficients(f) | Valuation(c, p) ge 0};
  assert IsPrime(p) and p ge 3;
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  if fp eq 0 then return false, false; end if;
  v := Valuation(Discriminant(f), p);
  fact := Factorization(fp);
  w := &+[Degree(a[1])*(a[2]-1) : a in fact];
  if Degree(fp) le 4 then w +:= 5-Degree(fp); end if;
  if v eq w then return true, not IsSquare(fp); end if;
  if p gt 5 then return false, false; end if;
  // can have wild ramification
  if Degree(fp) le 4 and Valuation(Coefficient(f, 6), p) gt 1 then
    return false, false;
  end if;
  for a in fact do
    if a[2] ge 2 then
      la := Parent(f)!ChangeUniverse(Coefficients(a[1]), Integers());
      r := f mod la;
      if r eq 0 or Min([Valuation(c, p) : c in Coefficients(r)]) ge 2 then
        return false, false;
      end if;
    end if;
  end for;
  return true, not IsSquare(fp);
end function;

// Arithmetic in Pic^0(C/F_p) for C as above and of genus 2
// Elements are represented as records with components a, b, d as usual, such that
// * a divides f - b^2
// * deg(a) le d le 2
// * deg(b) le 3; if deg(a) = d then deg(b) lt d
// * if z is a multiple root of f,
//   then (x-z)|a implies a = (x-z)^2 and b = c(x-z) with c /= (f(x)/(x-z)^2)(z)
// * zero is <1,0,0>

G2Div := recformat< a : RngUPolElt, b : RngUPolElt, d : RngIntElt >;

// could also put f and c = (f - b^2)/a into the data structure...

function Dnorm(pt)
  // normalize a divisor
  a := pt`a; b := pt`b; d := pt`d;
  a *:= 1/LeadingCoefficient(a);
  if Degree(a) eq d then
    b := b mod a;
  else
    // contributions at infinity
    bl := Parent(b)![Coefficient(b, i) : i in [0..Degree(a)+3-d]];
    b := b - bl + (bl mod a);
  end if;
  return rec<G2Div | a := a, b := b, d := d>;
end function;

// The following should work over any (exact) field
function Dres(f, pt)
  // reduce a divisor
  a := pt`a; b := pt`b; d := pt`d;
  a *:= 1/LeadingCoefficient(a);
  if d le 3 then return Dnorm(rec<G2Div | a := a, b := b, d := d>); end if;
  a1 := ExactQuotient(f - b^2, a);
  a1 *:= 1/LeadingCoefficient(a1);
  d1 := Degree(b) le 3 select 6 - d else d - 2;
  if Degree(a1) eq d1 then
    b1 := (-b) mod a1;
    return Dres(f, rec<G2Div | a := a1, b := b1, d := d1>);
  else
    // contributions at infinity
    bl := Parent(b)![Coefficient(b, i) : i in [0..Degree(a1)+1]];
    b1 := -((b-bl) + (bl mod a1));
    return Dres(f, rec<G2Div | a := a1, b := b1, d := d1>);
  end if;
end function;

function Dzero(f)
  return rec<G2Div | a := Parent(f)!1, b := Parent(f)!0, d := 0>;
end function;

// Copied from old version of jacobian.m:

function Dcomp(a1, b1, a2, b2, f)
  // special case: hit singularity in a1 and a2
  // singularity at infinity: dealt with in Dadd separately
  x := Parent(f).1;
  if a1 eq a2 and Degree(GCD([a1, f, Derivative(f)])) gt 0 then
    z := -Coefficient(a1, 1)/2; // singular point
    c1 := Coefficient(b1 mod a1, 1);
    c2 := Coefficient(b2 mod a2, 1);
    // pt1 = <(x-z)^2, c1*(x-z)>, pt2 = <(x-z)^2, c2*(x-z)>
    if c1 + c2 eq 0 then
      return Parent(f)!1, Parent(f)!0;
    else
      alpha := Evaluate(ExactQuotient(f, (x-z)^2), z);
      return (x-z)^2, (alpha + c1*c2)/(c1 + c2)*(x-z);
    end if;
  end if;
  if a1 eq a2 and b1 eq b2 then
    // point doubling
    d, h1, h3 := XGCD(a1, 2*b1);
    a := (a1 div d)^2;
    b := (b1 + h3*((f - b1^2) div d)) mod a;
  else
    d0, _, h2 := XGCD(a1, a2);
    if d0 eq 1 then
      a := a1*a2; b := (b2 + h2*a2*(b1-b2)) mod a;
    else
      d, l, h3 := XGCD(d0, b1 + b2);
      a := (a1*a2) div d^2;
      b := (b2 + l*h2*(b1-b2)*(a2 div d) + h3*((f - b2^2) div d)) mod a;
    end if;
  end if;
  return a, b;
end function;

function Dadd(f, pt1, pt2)
  // Add two points using Cantor's algorithm (Math. Comp. 48, 95-101 (1987)),
  // generalized to the case y^2 = f(x) with deg(f) even and genus = 2.
  P := Parent(f);
  x := P.1;
  a1 := pt1`a; b1 := pt1`b; di1 := pt1`d - Degree(a1);
  a2 := pt2`a; b2 := pt2`b; di2 := pt2`d - Degree(a2);
  fi := P!Reverse(Eltseq(f) cat [0 : i in [Degree(f)+1..6]]);
  // first split into finite and infinite parts
  if di1 gt 0 then // there is something at infty
    b1f := b1 mod a1; 
    a1i := x^di1;
    b1i := (P!Reverse(Eltseq(b1) cat [0:i in [Degree(b1)+1..3]])) mod a1i; 
  else
    b1f := b1; b1i := P!0; a1i := P!1;
  end if;
  if di2 gt 0 then
    b2f := b2 mod a2; 
    a2i := x^di2;
    b2i := (P!Reverse(Eltseq(b2) cat [0:i in [Degree(b2)+1..3]])) mod a2i; 
  else
    b2f := b2; b2i := P!0; a2i := P!1;
  end if;
  // first step: composition
  af, bf := Dcomp(a1, b1f, a2, b2f, f);
  if di1 eq 0 and di2 eq 0 then
    a := af; b := bf; d := Degree(af);
  else
    ai, bi := Dcomp(a1i, b1i, a2i, b2i, fi);
    a := af;
    bi := P!Reverse(Eltseq(bi) cat [0 : i in [Degree(bi)+1..3]]); 
    b := bf + bi - (bi mod a);
    d := Degree(af) + Degree(ai);
  end if;
  // second step: reduction
  return Dres(f, rec<G2Div | a := a, b := b, d :=d>);
end function;

function Dneg(f, pt)
  return rec<G2Div | a := pt`a, b := -pt`b, d := pt`d>;
end function;

function Dred(f, pt, p)
  // reduction mod p for divisors of degree <= 3
  a0 := pt`a; b0 := pt`b; d := pt`d;
  P := Parent(f);
  PZ := PolynomialRing(Integers());
  PF := PolynomialRing(GF(p));
  a := PZ!(LCM([Integers() | Denominator(c) : c in Coefficients(a0)])*a0);
  bden := LCM([Integers() | Denominator(c) : c in Coefficients(b0)]);
  b := PZ!(bden*b0);
  if IsDivisibleBy(bden, p) then
    as := Eltseq(a) cat [ 0 : i in [Degree(a)+1..d] ];
    mat := Matrix([[0 : i in [1..j]] cat as cat [0 : i in [1..3-d-j]]
                     : j in [0..3-d]]);
    matp := ChangeRing(mat, GF(p));
    V := KSpace(GF(p), 4);
    VZ := RSpace(Integers(), 4-d);
    n := Valuation(bden, p);
    while n gt 0 do
      bs := Eltseq(b) cat [ 0 : i in [Degree(b)..2] ];
      flag, sol := IsConsistent(matp, V!bs);
      if not flag then
        assert d ge 2;
        if d eq 2 then
          return Dzero(PF!f);
        else // now d eq 3
          ap := PF!a;
          if Degree(ap) le d-2 then
            // problem at infinity -> move to zero
            fi := P![Coefficient(f, 6-i) : i in [0..6]];
            ai := P![Coefficient(a0, d-i) : i in [0..d]];
            bi := P![Coefficient(b0, 3-i) : i in [0..3]];
            dri := Dred(fi, rec<G2Div | a := ai, b := bi, d := d>, p);
            dr := dri`d;
            return Dres(PF!f, rec<G2Div |  a := PF![Coefficient(dri`a, dr-i)
                                                    : i in [0..dr]],
                                           b := PF![Coefficient(dri`b, 3-i)
                                                    : i in [0..3]],
                                           d := dr>);
          end if;
          // here Degree(ap) ge d-1
          ap1 := GCD(ap, Derivative(ap));
          // ap = (x - z)^2 apr 
          z := Roots(ap1)[1,1];
          apr := ExactQuotient(ap, (PF.1 - z)^2);
          apr *:= 1/LeadingCoefficient(apr);
          if Degree(apr) gt 0 then
            v := Evaluate(PF!f, z);    // y^2-coordinate
            P2 := PolynomialRing(Rationals(), 2);
            ypol := Evaluate(Resultant(P2.2-Evaluate(b0, P2.1),
                                       Evaluate(a, P2.1),
                                       P2.1),
                             [0, P.1]);
            ypol := PF!(1/LeadingCoefficient(ypol)*ypol);
            yval := -Coefficient(ExactQuotient(ypol, PF.1^2-v), 0);
            return rec<G2Div | a := apr, b := PF!yval, d := 1>;
          else
            // third point is at infinity
            if z eq 0 then
              // shift away
              a := Evaluate(a, P.1 - 1);
              b0 := Evaluate(b0, P.1 - 1);
              f := Evaluate(f, P.1 - 1);
              z := GF(p)!1;
            end if;
            // move infty to zero
            a := P![Coefficient(a, 3-i) : i in [0..3]];
            b0 := P![Coefficient(b0, 3-i) : i in [0..3]];
            f := P![Coefficient(f, 6-i) : i in [0..6]];
            z := 1/z;
            // now all relevant y-coordinates are finite mod p
            v := Evaluate(PF!f, z);
            P2 := PolynomialRing(Rationals(), 2);
            ypol := Evaluate(Resultant(P2.2-Evaluate(b0, P2.1),
                                       Evaluate(a, P2.1),
                                       P2.1),
                             [0, P.1]);
            ypol := PF!(1/LeadingCoefficient(ypol)*ypol);
            yval := -Coefficient(ExactQuotient(ypol, PF.1^2-v), 0);
            return rec<G2Div | a := PF!1, b := yval*PF.1^3, d := 1>;
          end if;
        end if;
      end if;
      b -:= PZ!Eltseq((VZ!sol)*mat);
      b0 -:= Parent(f)!Eltseq((VZ!sol)*mat)/p^n;
      b := ExactQuotient(b, p);
      bden := ExactQuotient(bden, p);
      n -:= 1;
    end while;
  end if;
  return Dres(PF!f, rec<G2Div | a := PF!a, b := (GF(p)!bden)^-1*PF!b, d := d>);
end function;

function Dmul(f, n, pt)
  if n eq 0 then return Dzero(f); end if;
  if n lt 0 then n := -n; pt := Dneg(f, pt); end if;
  r := Dzero(f);
  // n*pt + r is invariant
  while n gt 1 do
    if IsOdd(n) then r := Dadd(f, r, pt); end if;
    n div:= 2; 
    // pt +:= pt;
    pt := Dadd(f, pt, pt);
  end while;
  return Dadd(f, pt, r);
end function;

function PointtoDiv(f, pt)
  P := Parent(f); x := P.1;
  if pt[3] eq 0 then
    return rec<G2Div | a := P!1, b := pt[2]/pt[1]^3*x^3, d := 1>;
  else
    return rec<G2Div | a := x - pt[1]/pt[3], b := P!(pt[2]/pt[3]^3), d := 1>;
  end if;
end function;

function JacPttoDiv(ptJ)
  return rec<G2Div | a := ptJ[1], b := ptJ[2], d := ptJ[3]>;
end function;

function Drand(f)
  P := Parent(f);
  F := CoefficientRing(P);
  x := P.1;
  if f eq 0 then
    s := Random([0..#F]);
    repeat z := Random(F); until z ne 0;
    if s eq #F then
      return rec<G2Div | a := P!1, b := z*x^2, d := 2>; 
    else
      s := Random(F);
      return rec<G2Div | a := (x - s)^2, b := z*(x-s), d := 2>;
    end if;
  end if;
  sing := {<r[1], F!1> : r in Roots(GCD(f, Derivative(f)))};
  if Degree(f) le 4 then Include(~sing, <F!1, F!0>); end if;
  if not IsEmpty(sing) and Random([0..4]) eq 0 then
    s := Random(sing);
    if s[2] eq 0 then
      v := Coefficient(f, 4);
    else
      v := Evaluate(ExactQuotient(f, (x-s[1])^2), s[1]);
    end if;
    repeat z := Random(F); until z^2 ne v;
    if s[2] eq 0 then
      return rec<G2Div | a := P!1, b := z*x^2, d := 2>;
    else
      return rec<G2Div | a := (x - s[1])^2, b := z*(x - s[1]), d := 2>;
    end if;
  end if;
  bad := GCD(f, Derivative(f));
  sq, fb := IsSquare(f);
  while true do
    // take a random polynomial of degree 2
    repeat
      a := P![ Random(F) : i in [0..2] ];
      if a eq 0 then return Dzero(f); end if;
      a *:= 1/LeadingCoefficient(a);
    until GCD(a, bad) eq 1 and (Degree(f) ge 5 or Degree(a) eq 2);
    // for each factor, find a point on the curve of corresponding
    //  degree (if possible) and put them together
    case Degree(a):
      when 2:
        ra := Roots(a);
        if IsEmpty(ra) then
          // a is irreducible
          FE<w> := ext< F | a >;
          PE<y> := PolynomialRing(FE : Global := false);
          rs := Roots(y^2 - Evaluate(f,w));
          if not IsEmpty(rs) then
            b := P!Eltseq(Random(rs)[1]);
            if not (sq and (IsDivisibleBy(b + fb, a) or IsDivisibleBy(b - fb, a))) then
              // not on the same component if f is a square 
              return rec<G2Div | a := a, b := b, d := 2>;
            end if;
          end if;
        else
          // a splits into two linear factors
          PE<y> := PolynomialRing(F : Global := false);
          x1 := ra[1][1];
          rs1 := Roots(y^2 - Evaluate(f,x1));
          if not IsEmpty(rs1) then
            y1 := Random(rs1)[1];
            if #ra eq 1 and not sq then
              // a is the square of a linear polynomial
              if 2*y1 ne 0 then
                df1 := Evaluate(Derivative(f),x1);
                return rec<G2Div | a := a, b := y1+(df1/(2*y1))*(x-x1), d := 2>;
              end if;
            else
              // a is the product of two distinct linear factors
              x2 := ra[2][1];
              rs2 := Roots(y^2 - Evaluate(f,x2));
              if not IsEmpty(rs2) then
                y2 := Random(rs2)[1];
                b := ((y1-y2)*x + (x1*y2-x2*y1))/(x1-x2);
                return rec<G2Div | a := a, b := b, d := 2>;
              end if;
            end if;
          end if;
        end if;
      when 1:
        // a is linear -- must use one point at infinity
        PE<y> := PolynomialRing(F : Global := false);
        x1 := -Coefficient(a,0);
        rs1 := Roots(y^2 - Evaluate(f,x1));
        if not IsEmpty(rs1) then
          flag, rt := IsSquare(Coefficient(f, 6));
         if flag then
            y1 := Random(rs1)[1];
            y2 := Random({rt, -rt}); // y-coordinate of point at infty
            return rec<G2Div | a := a, b := y1+y2*(x^3-x1^3), d := 2>;
          end if;
        end if;
      when 0:
        // a is constant -- must use twice a point at infinity
        if not sq then
          PE<y> := PolynomialRing(F : Global := false);
          flag, rt := IsSquare(Coefficient(f, 6));
          if  flag then
            yinf := Random({rt, -rt}); // y-coordinate of point at infty
            if 2*yinf ne 0 then
              df := Coefficient(f,5)/(2*yinf);
              return rec<G2Div | a := P!1, b := yinf*x^3 + df*x^2, d := 2>;
            end if;
          end if;
        end if;
    end case;
  end while;
end function;

function BadOrder(f, p)
  // corrected: removed factor 3 when f is a nonzero square
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  if fp eq 0 then return p^2; end if; // purely additive
  fact := Factorization(fp);
  mults := {* a[2]^^Degree(a[1]) : a in fact *};
  if Degree(fp) lt 6 then mults join:= {* (6-Degree(fp))^^1 *}; end if;
  case mults:
    when {* 1, 1, 1, 1, 1, 1 *}:
      error "BadOrder: p =", p, "is a good prime for f =", f;
    when {* 1, 1, 1, 1, 2 *}:
      // C mod p has a node
      if Degree(fp) le 4 then
        a := Coefficient(fp, 4);
        E := HyperellipticCurveOfGenus(1, fp);
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 2]), 0);
        fq := ExactQuotient(fp, (PF.1-z)^2);
        a := Evaluate(fq, z);
        E := HyperellipticCurveOfGenus(1, fq);
      end if;
      return (#E)*(IsSquare(a) select p-1 else p+1);
    when {* 1, 1, 1, 3 *}:
        // a cusp
        if Degree(fp) eq 3 then
          qu := PF!1;
        else
          z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 3]), 0);
          qu := (PF.1 - z)^2;
        end if;
        return (#HyperellipticCurveOfGenus(1, ExactQuotient(fp, qu)))*p;
    when {* 1, 1, 2, 2 *}:
      // two nodes
      // find action of Frob on H_1(bouquet of two circles)
      gcd := &*[a[1] : a in fact | a[2] eq 2];
      disc := Discriminant(gcd);
      if IsSquare(disc) then
        // two nodes individually defined / F_p
        rs := [Evaluate(ExactQuotient(fp, (PF.1-z)^2), z) where z := r[1]
                : r in Roots(gcd)];
        o1 := IsSquare(rs[1]) select p-1 else p+1;
        o2 := #rs eq 1 select
               (IsSquare(Coefficient(fp, 4)) select p-1 else p+1)
              else (IsSquare(rs[2]) select p-1 else p+1);
        return o1*o2;
      else
        // nodes conjugate, defined over F_{p^2}
        if IsSquare(Evaluate(ExactQuotient(fp, gcd^2), 
                    Rep(Roots(gcd, GF(p,2)))[1]))
        then
          return p^2 - 1;
        else
          return p^2 + 1;
        end if;
      end if;
    when {* 2, 2, 2 *}:
      // three nodes (which may be conjugate to some degree),
      s := IsSquare(LeadingCoefficient(fp)); // decides on c_p
      degs := {* Degree(a[1]) : a in fact | a[2] eq 2 *};
      if &+degs lt 3 then degs join:= {* 1 *}; end if;
      case degs:
        when {* 1, 1, 1 *}:
          return s select (p-1)^2 else (p+1)^2;
        when {* 1, 2 *}:
          return p^2-1;
        when {* 3 *}:
          return s select (p^2+p+1) else (p^2-p+1);
        else
          error "Error in BadOrder, case 3 nodes.\n";
      end case;
    when {* 1, 2, 3 *}: // node + cusp
      if Degree(fp) eq 4 then
        s := IsSquare(Coefficient(fp, 4));
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 2]), 0);
        s := IsSquare(Evaluate(ExactQuotient(fp, (PF.1-z)^2), z));
      end if;
      return s select p*(p-1) else p*(p+1);
    when {* 1, 1, 4 *}: // tacnode
      if Degree(fp) eq 2 then
        s := IsSquare(Coefficient(fp, 2));
      else
        z := -Coefficient(Rep([a[1] : a in fact | a[2] eq 4]), 0);
        s := IsSquare(Evaluate(ExactQuotient(fp, (PF.1-z)^4), z));
      end if;
      return s select p*(p-1) else p*(p+1);
    when {* 3, 3 *}: // two cusps
      return p^2;
    when {* 2, 4 *}: // node & tacnode
      s := IsSquare(LeadingCoefficient(fp));
      return s select p*(p-1) else p*(p+1);
    when {* 1, 5 *}: // (2,5)-cusp
      return p^2;
    when {* 6 *}:
      // y^2 = l^6
      // s := IsSquare(LeadingCoefficient(fp));
      return p^2;
    else
      error "BadOrder: Case ",mults,"not yet implemented.\n";
  end case;
end function;

function MakeGroup(f, p)
  PF := PolynomialRing(GF(p));
  fp := PF!f;
  return <func< | Drand(fp)>,                  // random point
          Dzero(fp),                           // zero
          func<pt1, pt2 | Dadd(fp, pt1, pt2)>, // addition
          func<n, pt | Dmul(fp, n, pt)>,       // scalar multplication
          BadOrder(f, p),                      // group order
          func<pt | <PF!pt`a, PF!pt`b, pt`d>>        // extract a comparable object
         >;
end function;

///////////////////////
//                   //
//  Group structure  //
//                   //
///////////////////////

// Find the group structure of the rational points on the Jacobian
// over a finite field.

function MypSubgroup(Gr, p)
// Computes the p-subgroup of the abelian group
//  Gr = <rand, zero, add, mul, ord, extract>
// where rand() gives a random element of Gr, add(g,h) adds g and h in Gr
// and mul(n, g) computes n*g in Gr and ord = #Gr (supposed to be known)
    rand := Gr[1];
    zero := Gr[2];
    add := Gr[3];
    mul := Gr[4];
    order := Gr[5];
    extract := Gr[6];
    e := Valuation(order, p);
    if e eq 0 then
      G := AbelianGroup([]);
      return G, func<g | zero>;
    end if;
    d := order div p^e;
    // Find points in the p-subgroup
    curr_size := 0; // logarithmic
    end_size := e;
    // generators found so far, with their relations
    gens := [];
    rels := [];
    // points lists all the points in the current subgroup,
    // with base representations listed in reps
    points := [ extract(zero) ];
    points1 := [ zero ];
    reps := [ [] ];
    while curr_size lt end_size do
      // find a random point in the p-subgroup
      rpt := rand();
      new_pt := mul(d, rpt);
      // check if already in current subgroup
      if extract(new_pt) notin points then
        q := mul(p, new_pt);
        f := 1;
        pos := Position(points, extract(q));
        while pos eq 0 do
          q := mul(p, q);
          pos := Position(points, extract(q)); 
          f +:= 1;
          assert f + curr_size le end_size;
        end while;
        // now p^f*new_pt is in the known subgroup
        // treat the special case that the first try already generates
        if extract(q) eq extract(zero) and IsEmpty(gens) and f eq e then
          G<[P]> := AbelianGroup([p^e]);
          return G, func< g | mul(s[1], new_pt)  where s := Eltseq(g) >;
        end if;
        // get its base rep
        rep := reps[pos];
        // enlarge gens
        Append(~gens, new_pt);
        rels := [ r cat [0] : r in rels ] cat [ rep cat [-p^f] ];
        // enlarge current subgroup
        curr_size +:= f;
        if curr_size eq end_size then break; end if;
        new_points := [];
        new_points1 := [];
        new_reps := [];
        pta := zero;
        for i := 0 to p^f-1 do
          for z in points1 do
            npt := add(z, pta);
            Append(~new_points, extract(npt));
            Append(~new_points1, npt);
          end for;
          new_reps cat:= [ r cat [i] : r in reps ];
          pta := add(pta, new_pt);
        end for;
        points := new_points;
        points1 := new_points1;
        reps := new_reps;
      end if;
    end while;
    // Now construct the group
    GF<[t]> := FreeAbelianGroup(#gens);
    G<[P]>, proj
       := quo< GF | [ &+[ r[i]*t[i] : i in [1..#r] ] : r in rels ] >;
    new_gens := [];
    function linc(cofs, elts)
      res := zero;
      for i := 1 to #cofs do
        res := add(res, mul(cofs[i], elts[i]));
      end for;
      return res;
    end function;
    for i := 1 to #Generators(G) do
      s := Eltseq(G.i @@ proj);
      Append(~new_gens, linc(s, gens));
    end for;
    return G, func< g | linc(Eltseq(g), new_gens) >;
end function; 

function MyAbelianGroup(Gr)
    rand := Gr[1];
    zero := Gr[2];
    add := Gr[3];
    mul := Gr[4];
    order := Gr[5];
    function linc(cofs, elts)
      res := zero;
      for i := 1 to #cofs do
        res := add(res, mul(cofs[i], elts[i]));
      end for;
      return res;
    end function;
    fo := Factorization(order);
    ed := [];
    gL := [];
    for tr in fo do
      Gp, m := MypSubgroup(Gr, tr[1]);
      Lp := [ m(Gp.i) : i in [1..#Generators(Gp)] ];
      inv := Invariants(Gp);
      error if #inv gt 1 and &or[ inv[i] gt inv[i+1] : i in [1..#inv-1] ],
            "Group returned by pSubgroup has unusual invariant ordering:",inv;
      d := #inv-#ed;
      if d gt 0 then
        ed := inv[[1..d]] cat [ Lcm(ed[i], inv[i+d]) : i in [1..#ed] ];
        gL := Lp[[1..d]] cat [ add(gL[i], Lp[i+d]) : i in [1..#gL] ];
      else
        ed := ed[[1..-d]] cat [ Lcm(ed[i-d], inv[i]) : i in [1..#inv] ];
        gL := gL[[1..-d]] cat [ add(gL[i-d], Lp[i]) : i in [1..#Lp] ];
      end if;
    end for;
    G<[P]> := AbelianGroup(ed);
    return G, func< g | linc(Eltseq(g), gL) >;
end function;

/////////////////////////////////////////////////////////////////////////

/************************************************************************
 * New version of GroupInfo etc. working with factored group orders
 *
 * Started 2008-10-29, M. Stoll
 ************************************************************************/

GIdeep := recformat< level : Integers(), // the current level (1 = flat info)
                     Kgens : SeqEnum,    // generators of kernel of red (in J)
                     Ker1 : SeqEnum,     // generators of kernel of red
                                         //  as coefficient seqs w.r.t. bas
                     Ker : SeqEnum       // generators of current kernel
                                         //  as coefficient seqs w.r.t. bas
                   >;

GIentry := recformat< p : Integers(),  // the prime at which information was obtained
                      imbas : SeqEnum, // image of basis
                      imC : SetEnum,   // image of curve
                      invs : SeqEnum,  // invariants of group as exponent vectors
                      sizes : Assoc,   // hash table storing image sizes in quotients
                      deep : Rec       // record providing data for deep info
                    >;

GIrec := recformat< last : Integers(), // last prime used
                    pl : SeqEnum,      // list of relevant primes
                    rank : Integers(), // the rank of the MW group
                    J : JacHyp,        // the Jacobian
                    K : SrfKum,        // its Kummer surface
                    DAM,               // the `dual action matrix'
                    badp : SetEnum,    // the bad primes
                    bas : SeqEnum,     // generators of the MW group
                    hp,                // the height pairing matrix
                    deg3,              // data specifying embedding of curve in J
                    info : SeqEnum,    // actual information
                    maxfactors : SeqEnum, // orders of largest factors of product
                    bestfactor : SeqEnum  // factor giving best value 
                  >;

// For nice output...
function ending(n)
  if n eq 1 then return "st";
  elif n eq 2 then return "nd";
  elif n eq 3 then return "rd";
  else return "th";
  end if;
end function;

procedure printseq(seq)
  printf "[";
  for i := 1 to #seq do
    printf "%o", seq[i];
    if i lt #seq then printf ", "; end if;
  end for;
  printf "]";
end procedure;

//-----------------------------------------------------------------------------
// Construct the injection C(F_p) --> J(F_p) --> G
// given by P |--> [P + M - D], M = polar divisor of x, D = point of degree 3;
// G is an abstract abelian group isomorphic with J(F_p)
// deg3 = G2Div record (with d = 1 or d = 3), already reduced mod p
function MakeInj(Jp, p, deg3)
  Cp := Curve(Jp);
  f := HyperellipticPolynomials(Cp);
  a := deg3`a;
  b := deg3`b;
  if deg3`d eq 1 then
    if Degree(a) eq 1 then
      x0 := -Coefficient(a,0)/Coefficient(a,1);
      y0 := Evaluate(b, x0);
      ptp := Cp![x0, y0];
    else
      ptp := Cp![1, Coefficient(b, 3), 0];
    end if;
    return func<pt | (Cp!pt) - ptp>;
  end if;
  ra := Roots(a);
  if not IsEmpty(ra) then
    r := ra[1,1]; // one root
    a1 := ExactQuotient(a, Parent(a).1 - r);
    pt1 := Cp![r, Evaluate(b, r)];
    ptJ := elt<Jp | a1, b, Degree(f) eq 5 select Degree(a1) else 2>;
    return func<pt | (pt - pt1) - ptJ>;
  end if;
  if Degree(a) le 2 then
    // "root" at infinity
    pt1 := Cp![1, Coefficient(b, 3), 0];
    ptJ := elt<Jp | a, b, Degree(f) eq 5 select Degree(a) else 2>;
    return func<pt | (pt - pt1) - ptJ>;
  end if;
  // otherwise, a is irreducible; use arithmetic of divisors
  return func<pt | elt<Jp | impt`a, impt`b,
                            Degree(f) eq 5 select Degree(impt`a) else impt`d>
                    where impt := Dadd(f, PointtoDiv(f, pt), Dneg(f, deg3))>;
end function;

procedure printfact(seq, pl)
  flag := true;
  for j := 1 to #pl do
    if seq[j] gt 0 then
      flag := false;
      printf " %o", pl[j];
      if seq[j] gt 1 then
        printf "^%o", seq[j];
      end if;
    end if;
  end for;
  if flag then printf " 1"; end if;
end procedure;

// Deal with one (good, odd) prime, return GIentry structure
// deg3 already reduced mod p
function InfoAtp(Jp, bas, deg3, pl, p)
  vprintf GroupInfo, 1: " GroupInfo: p = %o\n", p;
  Cp := Curve(Jp);
  pts := Points(Cp);
  vprintf GroupInfo, 2: "   Computing group structure...\n";
  s1, s2 := GetSeed();
  G, m := AbelianGroup(Jp);
  vprintf GroupInfo, 2: "    ...done\n";
  I := Invariants(G);
  fI := [[Valuation(i, q) : q in pl] : i in I];
  if IsVerbose("GroupInfo", 2) then
    printf "   Invariants(G) = [";
    for j := 1 to #fI do
      printfact(fI[j], pl);
      if j lt #fI then printf " |"; end if;
    end for;
    printf " ]\n";
  end if;
  vprintf GroupInfo, 3: "   Constructing embedding...\n";
  inj := MakeInj(Jp, p, deg3);
  vprintf GroupInfo, 3: "   Setting up discrete log function...\n";
  DL := MakeDL(G, m); // This is still faster than  func<x | x @@ m>;
  vprintf GroupInfo, 2: "   Computing discrete logs...\n";
  imbas := [DL(Jp!b) : b in bas];
  imC := {DL(inj(pt)) : pt in pts};
  // restrict to image of MW group
  G1 := sub<G | imbas>;
  imbas := ChangeUniverse(imbas, G1);
  imC := {Eltseq(G1!c) : c in imC | c in G1};
  I := Invariants(G1);
  fI := [[Valuation(i, q) : q in pl] : i in I];
  sizes := AssociativeArray(Integers());
  sizes[#I ge 1 select I[#I] else 1] := #imC;
  vprintf GroupInfo, 2: "   done.\n";
  vprintf GroupInfo, 2: "   #C(F_%o) = %o\n", p, #imC;
  return rec<GIentry | p := p, imbas := imbas, imC := imC, invs := fI, sizes := sizes>;
end function;

// Compute info at bad, but regular odd prime (and such that f mod p is not a square)
function InfoAtBadRegularp(C, bas, deg3, pl, p)
  // deg3 = G2Div record, already reduced mod p
  vprintf GroupInfo, 1: " GroupInfo: p = %o (bad, but regular)\n", p;
  f := HyperellipticPolynomials(C);
  // construct group
  vprintf GroupInfo, 2: "   Computing group structure...\n";
  G := MakeGroup(f, p);
  A, mA := MyAbelianGroup(G);
  I := Invariants(A);
  fI := [[Valuation(i, q) : q in pl] : i in I];
  if IsVerbose("GroupInfo", 2) then
    printf "   Invariants(G) = [";
    for j := 1 to #fI do
      printfact(fI[j], pl);
      if j lt #fI then printf " |"; end if;
    end for;
    printf " ]\n";
  end if;
  // set up discrete log function
  vprintf GroupInfo, 3: "   Setting up discrete log function...\n";
  DL := MakeDL(A, mA, G[4], func<x,y | G[3](x, G[4](-1,y))> : extract := G[6]);
  // compute image of basis in A
  vprintf GroupInfo, 2: "   Computing discrete logs...\n";
  imbas := [DL(Dred(f, JacPttoDiv(b), p)) : b in bas];
  // find smooth points on C(F_p) (singularities don't lift since curve is regular)
  // and compute image in A
  fp := PolynomialRing(GF(p))!f;
  bad := {r[1] : r in Roots(GCD(fp, Derivative(fp)))};
  d3r := Dneg(fp, deg3); // subtract deg3 !
  inj := func<pt | Dadd(fp, PointtoDiv(fp, pt), d3r)>; // map C -> J
  imC := {};
  for a in GF(p) do
    if a notin bad then
      flag, r := IsSquare(Evaluate(fp, a));
      if flag then
        Include(~imC, DL(inj(<a, r, GF(p)!1>)));
        if r ne 0 then Include(~imC, DL(inj(<a, -r, GF(p)!1>))); end if;
      end if;
    end if;
  end for;
  flag, r := IsSquare(Coefficient(fp, 6));
  if Degree(fp) ge 5 and flag then
    // include points at infinity
    Include(~imC, DL(inj(<GF(p)!1, r, GF(p)!0>)));
    if r ne 0 then Include(~imC, DL(inj(<GF(p)!1, -r, GF(p)!0>))); end if;
  end if;
  // restrict to image of MW group
  A1 := sub<A | imbas>;
  imbas := ChangeUniverse(imbas, A1);
  imC := {Eltseq(A1!c) : c in imC | c in A1};
  I := Invariants(A1);
  fI := [[Valuation(i, q) : q in pl] : i in I];
  sizes := AssociativeArray(Integers());
  sizes[#I ge 1 select I[#I] else 1] := #imC;
  vprintf GroupInfo, 2: "   done.\n";
  vprintf GroupInfo, 2: "   #C(F_%o) = %o\n", p, #imC;
  return rec<GIentry | p := p, imbas := imbas, imC := imC, invs := fI, sizes := sizes>;
end function;

function ToDualKummer(f, pt)
  // maps a degree 3 or degree 1 divisor pt to the dual Kummer surface
  a := pt`a; b := pt`b; d := pt`d;
  if Type(CoefficientRing(a)) eq FldRat then
    function norm(seq)
      l := LCM([Denominator(a) : a in seq]);
      seq := [Numerator(a)*ExactQuotient(l, Denominator(a)) : a in seq];
      g := GCD(seq);
      return [ExactQuotient(a, g) : a in seq];
    end function;
  else
    function norm(seq)
      j := 1;
      while j le #seq and seq[j] eq 0 do j +:= 1; end while;
      return [a/seq[j] : a in seq];
    end function;
  end if;
  if d eq 1 then
    if Degree(a) eq 1 then
      return norm([x^2, -x, 1, 0]) where x := -Coefficient(a, 0);
    else
      return [CoefficientRing(Parent(f)) | 1,0,0,0];
    end if;
  end if;
  assert d eq 3;
  P := Parent(f);
  R := CoefficientRing(P);
  P4<[x]> := PolynomialRing(R, 4);
  al := &+[x[i]*Coefficient(a,i-1) : i in [1..4]];
  bl := &+[x[i]*Coefficient(b,i-1) : i in [1..4]];
  c := ExactQuotient(f - b^2, a);
  cl := &+[x[i]*Coefficient(c,i-1) : i in [1..4]];
  s1 := -x[2]^2 + x[1]*x[3];
  s2 := -x[2]*x[3] + x[1]*x[4];
  s3 := -x[3]^2 + x[2]*x[4];
  s4 := &+[Coefficient(f,i)*x[(i div 2)+1]*x[((i+1) div 2)+1] : i in [0..6]];
  mons := MonomialsOfDegree(P4, 2);
  q := al*cl + bl^2;
  mat := Matrix([[MonomialCoefficient(pol, m) : m in mons]
                   : pol in [q, s1, s2, s3, s4]]);
  ker := Kernel(mat);
  assert Dimension(ker) ge 1;
  assert Basis(ker)[1,1] ne 0;
  res := Eltseq(Basis(ker)[1]);
  res := [-res[i]/res[1] : i in [2..5]];
  return norm(res);
end function;

function TDK(f, deg3, lc, bas)
  // here deg3 = G2Div record with d = 1 or d = 3,
  // lc = sequence of coeffs for bas = sequence of points on Jac(y^2 = f(x))
  // computes image on dual Kummer surface of &+[lc[i]*bas[i] : i in [1..#bas]]
  ptJ := &+[lc[i]*bas[i] : i in [1..#bas]];
  pt := Dadd(f, deg3, rec<G2Div | a := ptJ[1], b := ptJ[2], d := ptJ[3]>);
  return ToDualKummer(f, pt);
end function;

function DistanceFromCurve(pt, p)
  return (Valuation(pt[4], p) + 1) div 2;
end function;


// Compute higher kernels of reduction. Use Kummer Surface and p-adic
// arithmetic.

function GetSubgroup(A, test)
  // A = free abelian group.
  // finds subgroup of A (assumed of finite index) on which test is true
  // (assuming this _is_ a subgroup!)
  bas := OrderedGenerators(A);
  gens := [];
  As := { A!0 }; // known part of quotient group
  for b in bas do
    // find smallest multiple of b such that As + b meets the subgroup
    j := 1; 
    bb := b;
    repeat
      flag := exists(a){ a : a in As | test(bb+a) };
      if not flag then
        j +:= 1;
        bb +:= b;
      end if;
    until flag;
    // note new kernel generator
    Append(~gens, bb + a);
    // extend As to get set of representatives of the image of the
    // group generated by the first few generators of A in the quotient
    As := { a + i*b : i in [0..j-1], a in As };
  end for;
  return sub< A | gens >;
end function;

function GoodReps(MW, ker, bas : hp := HeightPairingMatrix(bas))
  // gives sets of "small" representatives of the quotient by ker
  // ker given as subgroup of free abelian group MW on bas
  gmat := Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]] : i in [1..#bas]]);
  while not IsPositiveDefinite(gmat) do
    gmat +:= IdentityMatrix(Integers(), #bas);
  end while;
  L := LatticeWithGram(gmat);
  // get elements of quotient and lift to MW
  G, m := quo<MW | ker>;
  elts := {MW | g @@ m : g in G};
  // get generators of ker
  gens := ChangeUniverse(OrderedGenerators(ker), MW);
  // set up sublattice
  Ls := sub<L | [L | Eltseq(g) : g in gens]>;
  return {e - MW![Round(a) : a in Eltseq(ClosestVectors(Ls, L!Eltseq(e))[1])]
           : e in elts};
end function;

function InfoAtBadp(C, bas, deg3, pl, p, mat)
  // compute info mod p for really bad p.
  vprintf GroupInfo, 1: " GroupInfo: p = %o (very bad)\n", p;
  MW := FreeAbelianGroup(#bas);
  J := Universe(bas);
  f, h := HyperellipticPolynomials(C);
  assert h eq 0;
  fp := PolynomialRing(GF(p))!f;
  Jpeqns := JacEquations(fp);
  redpt := func< ptJ | ChangeUniverse(JPtToCoordsModN(ptJ, p), GF(p)) >;
  pt0 := redpt(J!0);
  test := func< pt | redpt(ptJ) eq pt0
                     where ptJ := &+[s[i]*bas[i] : i in [1..#bas]]
                     where s := Eltseq(pt) >;
  vprintf GroupInfo, 2: "   finding kernel of reduction...\n";
  K := GetSubgroup(MW, test);
  bas0 := [&+[s[i]*bas[i] : i in [1..#bas]] where s := Eltseq(b)
            : b in ChangeUniverse(OrderedGenerators(K), MW)];
     // basis of K0 as rational points on J
  G, qG := quo<MW | K>;
  imbas := [qG(b) : b in OrderedGenerators(MW)];
  // find image of curve
  reps := GoodReps(MW, K, bas : hp := mat); // representatives of quotient in MW
  function test1(b)
    coords := TDK(f, deg3, Eltseq(b), bas);
    if Valuation(coords[4], p) gt 0 then
      if Valuation(coords[3], p) eq 0 then
        // check if point mod p lifts to p-adic point
        x := -(GF(p)!coords[2])/GF(p)!coords[3];
        if p ne 2 then
          fx := Evaluate(ChangeRing(f, Integers()), x);
          if fx ne 0 then return IsSquare(fx); end if;
          // now p divides f(x)
        end if;
        return HasPoint(Evaluate(f, p*Parent(f).1 + Integers()!x), p);
      else
        // check for p-adic point reducing to infinity
        return HasPoint(Evaluate(Parent(f)![Coefficient(f,6-i) : i in [0..6]],
                                 p*Parent(f).1),
                                 p);
      end if;
    end if;
    return false;
  end function;
  imC := {qG(b) : b in reps | test1(b)};
  // restrict to image of MW group
  G1 := sub<G | imbas>;
  imbas := ChangeUniverse(imbas, G1);
  imC := {Eltseq(G1!c) : c in imC | c in G1};
  I := Invariants(G1);
  fI := [[Valuation(i, q) : q in pl] : i in I];
  if IsVerbose("GroupInfo", 2) then
    printf "   #C(F_%o) = %o\n", p, #imC;
    printf "   Invariants(G) = [";
    for j := 1 to #fI do
      printfact(fI[j], pl);
      if j lt #fI then printf " |"; end if;
    end for;
    printf " ]\n";
  end if;
  sizes := AssociativeArray(Integers());
  sizes[#I ge 1 select I[#I] else 1] := #imC;
  vprintf GroupInfo, 2: "   done.\n";
  return rec<GIentry | p := p, imbas := imbas, imC := imC, invs := fI, sizes := sizes>;
end function;

//----------------------------------------------------------------------

// Logarithms

function LogSeries(f, s2, s1, n)
  f0,f1,f2,f3,f4,f5,f6 := Explode([Coefficient(f, i) : i in [0..6]]);
  // taken from Victor Flynn's files
  log1 := s2
           + (n ge 3 select 1/3*f5*s1^3 - 2/3*f2*s2^3 else 0)
           + (n ge 5 select
              (2/5*f3*f6 - 3/5*f4*f5)*s1^5 + 2*f2*f6*s1^4*s2 + 4*f1*f6*s1^3*s2^2
               + (12*f0*f6 + f1*f5)*s1^2*s2^3 + 5*f0*f5*s1*s2^4
               + (12/5*f0*f4 - 3/5*f1*f3 + 6/5*f2^2)*s2^5
               else 0)
           + (n ge 7 select
              (-4/7*f1*f6^2 + 20/7*f2*f5*f6 - 8/7*f3*f4*f6 - 4/7*f3*f5^2
                + 10/7*f4^2*f5)*s1^7
               + (-4*f0*f6^2 + 7*f1*f5*f6 - 4*f2*f4*f6)*s1^6*s2
               + (18*f0*f5*f6 - 4*f1*f4*f6 + f1*f5^2)*s1^5*s2^2
               + (-4*f0*f4*f6 + 6*f0*f5^2 + 4*f1*f3*f6 - f1*f4*f5
                   - 4*f2^2*f6)*s1^4*s2^3
               + (16*f0*f3*f6 + 2*f0*f4*f5 - 8*f1*f2*f6)*s1^3*s2^4
               + (-24*f0*f2*f6 + 4*f0*f3*f5 - 3*f1*f2*f5)*s1^2*s2^5
               + (8*f0*f1*f6 - 14*f0*f2*f5 - f1^2*f5)*s1*s2^6
               + (-4/7*f0^2*f6 + 13/7*f0*f1*f5 - 64/7*f0*f2*f4 - 4/7*f0*f3^2
                   - 4/7*f1^2*f4 + 20/7*f1*f2*f3 - 20/7*f2^3)*s2^7
              else 0);
  log2 := s1
           + (n ge 3 select  -2/3*f4*s1^3 + 1/3*f1*s2^3 else 0)
           + (n ge 5 select
              (12/5*f2*f6 - 3/5*f3*f5 + 6/5*f4^2)*s1^5 + 5*f1*f6*s1^4*s2
               + (12*f0*f6 + f1*f5)*s1^3*s2^2 + 4*f0*f5*s1^2*s2^3
               + 2*f0*f4*s1*s2^4 + (2/5*f0*f3 - 3/5*f1*f2)*s2^5
               else 0)
           + (n ge 7 select
              (-4/7*f0*f6^2 + 13/7*f1*f5*f6 - 64/7*f2*f4*f6 - 4/7*f2*f5^2
                - 4/7*f3^2*f6 + 20/7*f3*f4*f5 - 20/7*f4^3)*s1^7
               + (8*f0*f5*f6 - 14*f1*f4*f6 - f1*f5^2)*s1^6*s2
               + (-24*f0*f4*f6 + 4*f1*f3*f6 - 3*f1*f4*f5)*s1^5*s2^2
               + (16*f0*f3*f6 - 8*f0*f4*f5 + 2*f1*f2*f6)*s1^4*s2^3
               + (-4*f0*f2*f6 + 4*f0*f3*f5 - 4*f0*f4^2 + 6*f1^2*f6
                   - f1*f2*f5)*s1^3*s2^4
               + (18*f0*f1*f6 - 4*f0*f2*f5 + f1^2*f5)*s1^2*s2^5
               + (-4*f0^2*f6 + 7*f0*f1*f5 - 4*f0*f2*f4)*s1*s2^6
               + (-4/7*f0^2*f5 + 20/7*f0*f1*f4 - 8/7*f0*f2*f3 - 4/7*f1^2*f3
                   + 10/7*f1*f2^2)*s2^7
              else 0);
  return [log1, log2];
end function;

// Find the precision (max. exponent) needed in a power series
// with Z_p coefficients to get p-adic precision prec for the
// integral, when plugging in something in p*Z_p

function precNeeded(p, prec)
  prec0 := prec;
  k := 1;
  pk := p;
  while pk lt k + prec do
    r := pk*Ceiling(prec/pk);
    if r lt k + prec then
      prec0 := r;
    end if;
    k +:= 1;
    pk *:= p;
  end while;
  return prec0;
end function;

// Compute the p-adic abelian logarithm in Q_p x Q_p of a point
// on the Jacobian in the kernel of reduction

function pAdicLogG2(ptJ, p, prec)
  // for now, ptJ is rational
  J := Parent(ptJ);
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  K := KummerSurface(J);
  // check that ptJ is in the kernel of reduction
  ptK := K!ptJ;
  assert forall{j : j in [1..3] | Valuation(ptK[j], p) ge 2};
  // trivial case
  Qp := pAdicField(p, prec);
  bigO := O(Qp!p^prec);
  if ptJ eq J!0 then return [Qp|0, 0]; end if;
  // find local coordinates at origin
  coords := JPttoCoords(ptJ);
  assert coords[1] ne 0;
  ll1 := Qp!coords[3]/Qp!coords[1];
  ll2 := Qp!coords[2]/Qp!coords[1];
  // check if precision of series is sufficient
  pr := Min(Valuation(ll1), Valuation(ll2));
  if prec lt 9*pr then
    if p eq 3 then
      if prec le 3*pr-1 then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);
      elif prec le 9*pr-2 then return LogSeries(f, ll1, ll2, 7);
      end if;
    elif p eq 5 then
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr-1 then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    elif p eq 7 then
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr-1 then return LogSeries(f, ll1, ll2, 5);
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    else
      if prec le 3*pr then return LogSeries(f, ll1, ll2, 1);
      elif prec le 5*pr then return LogSeries(f, ll1, ll2, 3);
      elif prec le 7*pr then return LogSeries(f, ll1, ll2, 5);
      elif prec le 9*pr then return LogSeries(f, ll1, ll2, 7);
      end if;
    end if;
  end if;
  // get components
  a := ptJ[1]; 
  b := ptJ[2];
  b1 := Coefficient(b, 1);
  // assert ptJ[3] eq 2;
  if Valuation(Coefficient(a, 1), p) ge 0 
      and Valuation(Coefficient(a, 0), p) ge 0
  then
    // relevant points have p-adically integral x-ccordinate
    xi := Qp!(-Coefficient(a, 1)/2);
    fxi := Evaluate(f, xi);
    if IsOdd(p) and Valuation(fxi) eq 0 then
      // p odd: use x-xi as local coordinate
      prec1 := precNeeded(p, Ceiling((p-1)/(p-2)*prec));
              // (p-1)/(p-2) to compensate for denominators in the square root
      Qp1 := pAdicField(p, prec1);
      xi := Qp!(-Coefficient(a, 1)/2);
      fxi := Evaluate(f, xi);
      del := xi^2 - Coefficient(a, 0);
        // disc/4, points have x = xi +- sqrt(del)
      Pws<t> := PowerSeriesRing(Qp1, prec1);
      f1 := Evaluate(f, t+xi)/fxi;
      diff1 := f1^(-1/2);
      diff2 := (t + xi)*diff1;
      log1 := Integral(diff1);
      log2 := Integral(diff2);
      l1 := &+[del^j*Coefficient(log1, 2*j+1) : j in [0..(prec1 div 2)-1]];
      l2 := &+[del^j*Coefficient(log2, 2*j+1) : j in [0..(prec1 div 2)-1]];
      s := Sqrt(del/fxi);
      if Valuation(b1*s-1) lt Valuation(b1*s+1) then s := -s; end if;
      return [(Qp!(s*l1)) + bigO, (Qp!(s*l2)) + bigO];
    else
      // use Kummer Surface
      pr2 := (4 + 5*Valuation(Discriminant(f), p))*prec;
      Kp := BaseChange(K, pAdicField(p, pr2));
      ptKp := Kp!ptK;
      mptK := p^(prec-1)*ptKp;
      needed := IsOdd(p) select 3*prec else 3*prec + 2;
      // if p = 2, we need a bit more, for the square root below
      assert forall{j : j in [1..3] | AbsolutePrecision(mptK[j]) ge needed};
      lls := [mptK[j]/p^(2*prec) : j in [1..3]];
      // lls = [l1^2, 2*l1*l2, l2^2]
      //  with l1, l2 = 1/p times the logs we want
      assert Valuation(lls[1]) le Valuation(lls[3]);
      l1 := Sqrt(lls[1]);
      l2 := lls[2]/(2*l1);
      l1 *:= p;
      l2 *:= p;
      // fix the sign
      if Valuation(ll1 + Qp!l1) gt Valuation(ll1 - Qp!l1) then
        l1 := -l1;
        l2 := -l2;
      end if;
      assert Valuation(ll1 - Qp!l1) gt Valuation(ll1)
              and Valuation(ll2 - Qp!l2) gt Valuation(ll1);
      return [(Qp!l1) + bigO, (Qp!l2) + bigO];
    end if;
  else
    // relevant points map to infinity mod p:
    // reduce to known case
    J1 := Jacobian(HyperellipticCurve(Parent(f)![Coefficient(f,6-i)
                                                  : i in [0..6]]));
    a1r := Parent(f)![Coefficient(a, 2-i) : i in [0..2]];
    b1r := (Parent(f)![0, 0, Coefficient(b, 1), Coefficient(b, 0)]) mod a1r;
    ptJ1 := elt<J1 | a1r, b1r, 2>;
    l := pAdicLogG2(ptJ1, p, prec);
    return [-l[2], -l[1]];
  end if;
end function;

//----------------------------------------------------------------------

procedure initDeep(~entry, bas, hp)
  // entry = GIentry record; the deep component will be set
  // bas = basis of MW group of J
  // hp = height pairing matrix of bas
  vprintf GroupInfo, 2: "  InitDeep(p = %o)...\n", entry`p;
  MW := FreeAbelianGroup(#bas);
  G := Universe(entry`imbas);
  K1 := Kernel(hom<MW -> G | entry`imbas>); // kernel of reduction
  gens1 := [MW!k : k in OrderedGenerators(K1)];
  gram := Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]] : i in [1..#bas]]);
  while not IsPositiveDefinite(gram) do gram +:= Parent(gram)!1; end while;
  L := LatticeWithGram(gram);
  // set up sublattice
  Lsub := LLL(sub<L | [L | Eltseq(g) : g in gens1]>);
  gens1 := [MW!Eltseq(b) : b in Basis(Lsub)];
  if IsVerbose("GroupInfo", 2) then
    printf "  Generators of kernel of red.: ";
    printseq([Eltseq(g) : g in gens1]);
    printf "\n";
  end if;
  J := Universe(bas);
  bas1 := [&+[J| es[i]*bas[i] : i in [1..#es]] where es := Eltseq(g) : g in gens1];
  vprintf GroupInfo, 2: "  ... computed as elements of MW group.\n";
  Ker := [Eltseq(g) : g in gens1];
  deep := rec<GIdeep | level := 1, Kgens := bas1, Ker1 := Ker, Ker := Ker>;
  entry`deep := deep;
end procedure;

function NextKernelOfReduction(entry)
  // entry = GIentry record
  // returns Ker component of the deep component for next level
  deep := entry`deep;
  p := entry`p;
  newlevel := deep`level + 1;
  Kgens := deep`Kgens;
  Ker1 := deep`Ker1;
  MW := FreeAbelianGroup(#entry`imbas);
  FK1 := FreeAbelianGroup(#Kgens);
  toMW := hom<FK1 -> MW | [MW!g : g in Ker1]>;
  G := AbelianGroup([p^newlevel, p^newlevel]);
  // compute logs
  logs := [ChangeUniverse(pAdicLogG2(b, p, newlevel), Integers()) : b in Kgens];
  if IsVerbose("GroupInfo", 2) then
    printf "  %o-adic logarithms mod %o^%o: ", p, p, newlevel;
    printseq(logs);
    printf "\n";
  end if;
  imgs := [G| l : l in logs];
  newker := toMW(Kernel(hom<FK1 -> G | imgs>));
  newKer := [Eltseq(MW!k) : k in OrderedGenerators(newker)];
  if IsVerbose("GroupInfo", 2) then
    printf "  Generators of %o%o kernel of reduction: ", newlevel, ending(newlevel);
    printseq(newKer);
    printf "\n";
  end if;
  return newKer;
end function;

//----------------------------------------------------------------------

// intrinsic LCInit(B::[JacHypPt])->SeqEnum
function LCInit(B)
  J := Universe(B);
  K := KummerSurface(J);
  V := [J!0];
  for j in B do
    V cat:= [j + v : v in V];
  end for;
  return [K!b : b in V];
end function;

// intrinsic LinearCombination(n::[RngIntElt],V::[SrfKumPt])->SrfKumPt
// V as given by LCInit
function LinearCombination(n, V)
  B := [V[2^(i-1)+1] :i in [1..#n]];
  for i in [1..#n] do
    V := [PseudoAddMultiple(V[j],B[i],V[j+1],n[i]) : j in [1..#V-1 by 2]];
  end for;
  assert #V eq 1;
  return V[1];
end function;

//----------------------------------------------------------------------
// Take some stuff from kummer.m and adapt it

// Given Kummer surface, get matrix of biquadratic forms giving action
// on the dual Kummer:
//
// If A = DualActionMatrix(K), x coordinates on dual Kummer, y coordinates on K,
// then  A(x,y) = w*z, with w and z the two possible images on the dual Kummer
// of the result of adding a lift of y (to J) to a lift of x (on Pic^1).
function DualActionMatrix(Kum)
  B := Kum`BBMatrix;
  PB := Parent(B[1,1]);
  v0 := [PB.i : i in [1..8]];
  PP := PolynomialRing(BaseField(Kum), 12);
  v1 := [PP.i : i in [1..4]];
  v2 := [PP.i : i in [5..8]];
  v3 := [PP.i : i in [9..12]];
  B := Matrix([[Evaluate(B[i,j], v2 cat v3) : j in [1..4]] : i in [1..4]]);
  expr := &+[v1[i]*B[i,j]*v1[j] : i,j in [1..4]];
  A := Matrix([[i eq j select Coefficient(expr, v3[i], 2)
                       else Coefficient(Coefficient(expr, v3[i], 1), v3[j], 1)/2
                 : j in [1..4]] : i in [1..4]]);
  // assert expr eq &+[v3[i]*Evaluate(A[i,j], v1 cat v2 cat [0,0,0,0])*v3[j] : i,j in [1..4]];
  return Matrix([[Evaluate(A[i,j], v0 cat [PB|0,0,0,0]) : j in [1..4]]
                  : i in [1..4]]);
end function;

function PseudoAddDual(P1, P2, P3, A)
  // P1 and P3 on dual Kummer (coordinate sequence), P2 in Kummer
  K := Parent(P2);
  i := K`SelectCoordinate(P3);
  L1 := Vector([P1[1]^2, P1[1]*P1[2], P1[1]*P1[3], P1[1]*P1[4], P1[2]^2,
                P1[2]*P1[3], P1[2]*P1[4], P1[3]^2, P1[3]*P1[4], P1[4]^2]);
  L2 := Vector([P2[1]^2, P2[1]*P2[2], P2[1]*P2[3], P2[1]*P2[4], P2[2]^2,
                P2[2]*P2[3], P2[2]*P2[4], P2[3]^2, P2[3]*P2[4], P2[4]^2]);
  c1 := 2*P3[i];
  cs := [(L1*A[i,j], L2) : j in [1..4]];
  L := [ j eq i select P3[i]*cs[i] else c1*cs[j] - P3[j]*cs[i] : j in [1..4] ];
  // assume p-adic numbers here...
  prec := Precision(Universe(L));
  v := Min([ Min(Valuation(x),prec) : x in L ]); // | x ne 0 ]);
  a := UniformizingElement(BaseField(K))^(-v);
  xs1 := [a*x : x in L];
  i := 1; while Valuation(xs1[i]) gt 0 do i +:= 1; end while;
  xs1 := [x/xs1[i] : x in xs1];
  return xs1;
end function;

function PseudoAddMultipleDual(P1, P2, P3, n, A)
  if n lt 0 then
    P3 := PseudoAddDual(P1, P2, P3, A); n := -n;
  end if;
  while true do
    if IsOdd(n) then
      P1 := PseudoAddDual(P1, P2, P3, A);
    else
      P3 := PseudoAddDual(P3, P2, P1, A);
    end if;
    n div:= 2;
    if n eq 0 then return P1; end if;
    P2 := Double(P2);
  end while;
end function;

function AddJPtDeg3ToDualKummer(pt, deg3)
  // deg3 = G2Div record <a, b, 3>
  f, h := HyperellipticPolynomials(Curve(Parent(pt)));
  F := CoefficientRing(Parent(f));
  assert h eq 0;
  sum := Dadd(f, rec<G2Div | a := pt[1], b := pt[2], d := pt[3]>, deg3);
  if sum`d le 1 then
    if Degree(sum`a) eq 0 then
      return [F | 1, 0, 0, 0];
    else
      x := -Coefficient(sum`a, 0);
      return [x^2, -x, 1, 0];
    end if;
  else
    return ToDualKummer(f, sum);
  end if;
end function;

function LCInitDual(deg3, B)
  // deg3 = G2Div record <a, b, 3>
  J := Universe(B);
  K := KummerSurface(J);
  V := [J!0];
  for j in B do
    V cat:= [j + v : v in V];
  end for;
  return [AddJPtDeg3ToDualKummer(-b, deg3) : b in V], ChangeUniverse(B, K);
end function;

// V as given by LCInitDual
function LinearCombinationDual(n, B, V, A)
  for i := 1 to #n do
    V := [PseudoAddMultipleDual(V[j],B[i],V[j+1],n[i],A) : j in [1..#V-1 by 2]];
  end for;
  assert #V eq 1;
  return V[1];
end function;

//----------------------------------------------------------------------

procedure DeepenLevel(~entry, ~GI)
  // entry: GIentry record (= GI`info[pos])
  bas := GI`bas;
  deg3 := GI`deg3;
  if not assigned GI`hp then GI`hp := HeightPairingMatrix(bas); end if;
  hp := GI`hp;
  if not assigned entry`deep then initDeep(~entry, bas, hp); end if;
  deep := entry`deep;
  level := deep`level;
  p := entry`p;
  n := level + 1;

  vprintf GroupInfo, 1: "  DeepenLevel for %o^%o...\n", p, n;
  
  // initialize K and DAM if necessary
  J := GI`J;
  if not assigned GI`K then
    GI`K := KummerSurface(J);
    A := DualActionMatrix(GI`K);
    vs := MonomialsOfDegree(CoefficientRing(A), 1);
    mons1 := [vs[1]^2, vs[1]*vs[2], vs[1]*vs[3], vs[1]*vs[4], vs[2]^2,
              vs[2]*vs[3], vs[2]*vs[4], vs[3]^2, vs[3]*vs[4], vs[4]^2];
    mons2 := [vs[5]^2, vs[5]*vs[6], vs[5]*vs[7], vs[5]*vs[8], vs[6]^2,
              vs[6]*vs[7], vs[6]*vs[8], vs[7]^2, vs[7]*vs[8], vs[8]^2];
    GI`DAM := [[Matrix([[MC(A[i,j], mons1[k]*mons2[l]) : l in [1..10]] : k in [1..10]])
                : j in [1..4]] : i in [1..4]]
                where MC := MonomialCoefficient;
  end if;
  K := GI`K;
  A := GI`DAM;

  // compute next kernel of reduction
  MW := FreeAbelianGroup(#bas);
  newKer := NextKernelOfReduction(entry);
  
  // work in quotient modulo nth kernel
  Kn := sub<MW | [MW!g : g in newKer]>;
  QG, qmap := quo<MW | Kn>;
  Qgens := [q @@ qmap : q in OrderedGenerators(QG)];
  
  // Compute "small" representatives of the quotient by Kn
  gram := Matrix([[Round(1000*hp[i,j]) : j in [1..#bas]] : i in [1..#bas]]);
  while not IsPositiveDefinite(gram) do gram +:= Parent(gram)!1; end while;
  L := LatticeWithGram(gram);
  // set up sublattice
  Ls := sub<L | [L | g : g in newKer]>;
  Qgens := [e - MW!Eltseq(ClosestVectors(Ls, L!Eltseq(e))[1]) : e in Qgens];
  if IsVerbose("GroupInfo", 2) then
    printf "  Generators of quotient by %o%o kernel: ", n, ending(n);
    printseq([Eltseq(g) : g in Qgens]);
    printf "\n";
  end if;
  assert [qmap(q) : q in Qgens] eq OrderedGenerators(QG);

  Qbas := [J | &+[J | es[i]*bas[i] : i in [1..#es]] where es := Eltseq(q)
             : q in Qgens];
  vprintf GroupInfo, 2: "  ... computed as points in MW group.\n";

  // some initializations for the computations on the dual Kummer
  V0 := LCInit(Qbas);
  V, B := LCInitDual(deg3, Qbas);
  v := Valuation(Discriminant(Curve(J)), p);
  Qp := pAdicField(p, 2*n+20+v); // 20 was 3 -- precision!
  Kp := BaseChange(K, Qp);
  B := ChangeUniverse(B, Kp);
  V0 := ChangeUniverse(V0, Kp);
  A := [[ChangeRing(m, Qp) : m in A1] : A1 in A];
  
  function norm(s)
    v := Min([Valuation(a) : a in s]);
    s := [a/p^v : a in s];
    i := 1; while Valuation(s[i]) gt 0 do i +:= 1; end while;
    return [a/s[i] : a in s];
  end function;
  V := [norm(ChangeUniverse(s, Qp)) : s in V];
  
  imbas := entry`imbas;
  G := Universe(imbas);
  h := hom<MW -> G | imbas>;
  assert sub<MW | [MW!g : g in deep`Ker]> eq Kernel(h);
  imQbas := [h(q) : q in Qgens]; // work with these...
  Qh := hom<QG -> G | imQbas>;
  imC := entry`imC;
  
  // map previous kernel of reduction into QG
  // note: image is usually 2-generated (instead of rank(MW)-generated)
  Knold := sub<QG | [qmap(MW!g) : g in deep`Ker]>;
  qgens := OrderedGenerators(Knold);
  
  // get images of representatives of imC in G on dual Kummer
  genses := [Eltseq(QG!b) : b in qgens];
  lcs := [[0 : b in Qbas]];
  for es in genses do
    lcs cat:= [[lc[i] + es[i] : i in [1..#es]] : lc in lcs];
  end for;
  
  function rep(a) // a : eltseq of element in G
    // compute lift r to QG and images of the relevant linear combinations
    //  r - e_1 P_1 - ... - e_g P_g, where P_1, ..., P_g are generators of 
    // the image of the previous kernel of reduction in QG.
    r := Eltseq((G!a) @@ Qh);
    Vr := [LinearCombinationDual([r[i] - lc[i] : i in [1..#r]], B, V, A) : lc in lcs];
    // check that point on dual Kummer (= Vr[1]) is on the curve mod p^(n-1)
    assert Valuation(Vr[1,4]) ge 2*level
            and Valuation(Vr[1,2]^2 - Vr[1,1]*Vr[1,3]) ge level;
    return <QG!r, Vr>;
  end function;
  imCplus := {rep(pt) : pt in imC};
  
  // set up next level of B
  B := [LinearCombination(es, V0) : es in genses];
  // check
  assert forall{b : b in B | Min([Valuation(b[i]) : i in [1..3]]) ge 2*level};
   
  imC := {};
  for pair in imCplus do
    // construct linear form
    vprintf GroupInfo, 3: "  lift(%o), v(e4) = %o, v(del) = %o\n",
                          Eltseq(pair[1]), Valuation(pair[2,1,4]),
                          Valuation(pair[2,1,2]^2 - pair[2,1,1]*pair[2,1,3]);
    z0 := GF(p)!((pair[2,1,2]^2 - pair[2,1,1]*pair[2,1,3])/p^level);
    if IsEmpty(qgens) then
      flag := z0 eq 0;
      if flag then solns := {[]}; end if;
    else
      mat := Matrix([[(GF(p)!((pt[2]^2 - pt[1]*pt[3])/p^level)) - z0]
                    where pt := LinearCombinationDual(Eltseq(g), B, pair[2], A)
                                : g in qgens]);
      // vprintf GroupInfo, 3: "  z0 = %o, mat = %o\n", z0, Eltseq(mat);
      flag, sol, ker := IsConsistent(mat, Vector([-z0]));
      if flag then solns := {sol + k : k in ker}; end if;
    end if;
    if not flag then
      vprintf GroupInfo, 3: "   no solution\n";
    else
      vprintf GroupInfo, 3: "   %o solution%o\n",
                            #solns, #solns eq 1 select "" else "s";
      for s in solns do
        r := ChangeUniverse(Eltseq(s), Integers());
        s1 := Knold!r;
        imDK := LinearCombinationDual(r, B, pair[2], A);
        // check
        assert Valuation(imDK[4]) ge n
                and Valuation(imDK[2]^2 - imDK[1]*imDK[3]) ge n;
        // change this so that it increases precision and recomputes
        // if there is precision loss:
        assert forall{j : j in [1..4] | AbsolutePrecision(imDK[j]) gt 2*n};
        if Valuation(imDK[4]) ge 2*n then
          Include(~imC, Eltseq(pair[1] + QG!s1));
        end if;
      end for;
    end if;
  end for;

  vprintf GroupInfo, 2: "Level %o: #points = %o\n", n, #imC;
  
  imbas := [qmap(MW.i) : i in [1..#bas]];
  // update structures
  entry`deep`level := n;
  entry`deep`Ker := newKer;
  entry`imbas := imbas;
  entry`imC := imC;
  I := Invariants(QG);
  fI := [[Valuation(i, q) : q in GI`pl] : i in I];
  if IsVerbose("GroupInfo", 2) then
    printf "   Invariants(G) = [";
    for j := 1 to #fI do
      printfact(fI[j], GI`pl);
      if j lt #fI then printf " |"; end if;
    end for;
    printf " ]\n";
  end if;
  sizes := AssociativeArray(Integers());
  sizes[#I ge 1 select I[#I] else 1] := #imC;
  entry`invs := fI;
  entry`sizes := sizes;
end procedure;

//---------------------------------------------------------------------------
// compute the relative size of the image of C in the group mod B
// returns updated entry as second value
procedure relsize(~entry, pl, Bvec, ~result)
  Is := entry`invs;
  if IsEmpty(Is) then result := 1.0; return; end if;
  Isred := [[Min(I[j], Bvec[j]) : j in [1..#Bvec]] : I in Is];
  Bvec := Isred[#Isred];
  Isnum := [&*[Integers() | pl[j]^I[j] : j in [1..#I]] : I in Isred];
  flag, size := IsDefined(entry`sizes, Isnum[#Isnum]);
  if not flag then
    // compute and store
    size := #{[c[j] mod Isnum[j] : j in [1..#c]] : c in entry`imC};
    entry`sizes[Isnum[#Isnum]] := size;
  end if;
  result := 1.0*size/&*Isnum;
end procedure;

// compute expected size of survivors set
procedure expsize(~GI, Bvec, ~result)
  Bnum := 1.0;
  pl := GI`pl;
  for j := 1 to #pl do
    Bnum *:= (1.0*pl[j])^Bvec[j];
  end for;
  Bnum := Bnum^(GI`rank);
  for j := 1 to #GI`info do
    relsize(~GI`info[j], pl, Bvec, ~f);
    Bnum *:= f;
  end for;
  result := Bnum;
end procedure;

morefactors := 5;

// construct initial GI object
function initGI(J, bas, deg3, SmoothBound)
  // deg3 = <a, b, d>
  pl := [p : p in [2..SmoothBound] | IsPrime(p)];
  bp := Set(BadPrimes(J));
  f, h := HyperellipticPolynomials(Curve(J));
  assert h eq 0;
  if Type(deg3) eq PtHyp then
    deg3 := PointtoDiv(f, deg3);
  else
    deg3 := rec<G2Div | a := Parent(f)!deg3[1], b := Parent(f)!deg3[2], d := deg3[3]>;
  end if;
  return rec<GIrec | last := 1, pl := pl, rank := #bas, J := J, bas := bas,
                     deg3 := deg3, info := [], badp := bp,
                     maxfactors := [[0 : j in [1..#bas+1+morefactors]]
                                     : i in [1..#pl]],
                     bestfactor := [0 : p in pl]>;
end function;

procedure sortin(~seq, val)
  // seq is sorted decreasingly
  for j := 1 to #seq do
    if val gt seq[j] then
      Insert(~seq, j, val);
      Prune(~seq);
      return;
    end if;
  end for;
end procedure;

procedure sortinreplace(~seq, val, old)
  // seq is sorted decreasingly
  for j := 1 to #seq do
    if val gt seq[j] then
      Insert(~seq, j, val);
      for k := j+1 to #seq do
        if old eq seq[k] then
          Remove(~seq, k);
          return;
        end if;
      end for;
      Prune(~seq);
      return;
    end if;
  end for;
end procedure;

// update GI structure with information in order to reach target eps
procedure computeGI(~GI, eps, ~short, testfun)
  // we assume target is not met with input GI
  r := GI`rank;
  pl := GI`pl;
  maxp := pl[#pl];
  J := GI`J;
  C := Curve(J);
  f := HyperellipticPolynomials(C);
  seenp := {entry`p : entry in GI`info};
  short := 0; // no "shortcut" proof with a single prime known (yet)
  t := 1.0;
  n := GI`last;
  repeat
    // find next prime to be used
    deepflag := false;
    flag := false;
    repeat
      n +:= 1;
      pp, p, k := IsPrimePower(n);
      if pp then
        if k gt 1 then
          flag := p in seenp and p le maxp and testfun(p, k);
          if flag then deepflag := true; end if;
        else
          if not p in GI`badp then
            Jp := BaseChange(J, GF(p));
            fact, rem := TrialDivision(#Jp, maxp);
            flag := IsEmpty(rem) and forall{a : a in fact | a[1] le maxp};
          elif p gt 2 and p le maxp
                and ((fl1 and fl2) where fl1, fl2 := IsRegularAtp(C, p))
          then
            fact, rem := TrialDivision(BadOrder(f, p), maxp);
            flag := IsEmpty(rem) and forall{a : a in fact | a[1] le maxp};
          else
            flag := p lt 10;
          end if;
        end if;
      end if;
    until flag;
    // compute info
    if deepflag then
      pos := Position([entry`p : entry in GI`info], p);
      assert pos gt 0;
      // increase level
      Isold := GI`info[pos]`invs;
      DeepenLevel(~GI`info[pos], ~GI);
      entry := GI`info[pos];
      if IsEmpty(entry`imC) then
        vprintf GroupInfo, 1: " Contradiction at p = %o, level = %o!\n",
                              p, entry`deep`level;
        short := p^entry`deep`level;
        return;
      end if;
      Is := entry`invs;
      // sort into maxfactors
      for j := 1 to #pl do
        for i := 1 to #Isold do
          sortinreplace(~GI`maxfactors[j], Is[i,j], Isold[i,j]);
        end for;
        for i := #Isold + 1 to #Is do
          sortin(~GI`maxfactors[j], Is[i,j]);
        end for;
      end for;
      GI`last := n;
    else
      deg3r := Dred(f, GI`deg3, p);
      if p in GI`badp then
        if IsOdd(p) and (fl2 where _, fl2 := IsRegularAtp(C, p)) then
          entry := InfoAtBadRegularp(C, GI`bas, deg3r, pl, p);
        else
          if not assigned GI`hp then GI`hp := HeightPairingMatrix(GI`bas); end if;
          entry := InfoAtBadp(C, GI`bas, GI`deg3, pl, p, GI`hp);
        end if;
      else
        entry := InfoAtp(Jp, GI`bas, deg3r, pl, p);
      end if;
      Append(~GI`info, entry);
      if IsEmpty(entry`imC) then
        vprintf GroupInfo, 1: " Contradiction at p = %o!\n", p;
        short := p;
        return;
      end if;
      Is := entry`invs;
      // sort into maxfactors
      for j := 1 to #pl do
        for I in Is do
          sortin(~GI`maxfactors[j], I[j]);
        end for;
      end for;
      Include(~seenp, p);
      GI`last := p;
    end if;
    if IsVerbose("GroupInfo", 3) then
      printf "  maxfactors:\n";
      for k := 1 to morefactors+1 do
        printf "    ";
        printfact([GI`maxfactors[j, r+k] : j in [1..#pl]], pl);
        printf "\n";
      end for;
    end if;
    // compute current target value
    expsize(~GI, GI`bestfactor, ~t); // new value for old bestfactor
    bf0 := GI`bestfactor;
    vprintf User3: "<%o", n;
    for k := 0 to morefactors do
      // look at B given by invariants of product group
      bf := [GI`maxfactors[j, r+1+k] : j in [1..#pl]];
      expsize(~GI, bf, ~t1);
      vprintf User3: ", %o", ChangePrecision(t1,4);
      if k eq 0 then t0 := t1; end if; // save for later
      if t1 lt t then
        t := t1;
        bf0 := bf;
      end if;
    end for;
    vprintf User3: ">,\n";
    GI`bestfactor := bf0;
    if IsVerbose("GroupInfo", 2) then
      printf "  bestfactor: ";
      printfact(GI`bestfactor, pl);
      printf "\n";
    end if;
    vprintf GroupInfo, 1: " ==> New target value is %o [%o]\n",
                          ChangePrecision(t, 4), ChangePrecision(t0, 6);
  until t le eps;
end procedure;

// findQSeq computes a `good' sequence of primes
// GI: group info structure
// eps: upper bound for expected size of set of candidates
procedure findQSeq(~GI, eps, ~result, ~Bvec)
  pl := GI`pl;
  max := GI`bestfactor;
  // optimze according to minimal expected size at B_i
  // if B_0 = 1, B_{i+1} = B_i*p_i
  // B in factored form
  agendas := [[<1, [0 : i in [1..#pl]], 1.0>]]; // entries <p, B, s>
  agendav := [1.0]; 
  reached := {[0 : i in [1..#pl]]}; // lists the values of B that have been seen so far
  while not IsEmpty(agendav) do
    v, pos := Min(agendav); // try to extend cheapest path so far
    l := agendas[pos];
    vprintf MWSieve, 2: "  findQSeq: l = %o,\n   v = %o\n",
                        [l[i,1] : i in [2..#l]], v;
    Remove(~agendas, pos);
    Remove(~agendav, pos);
    B := l[#l,2];
    s := l[#l,3];
    if s lt eps then 
      // reached success criterion
      vprintf MWSieve, 1: "    Multipliers: %o\n", [l[i,1] : i in [2..#l]];
      vprintf MWSieve, 1: "    Predicted sizes: %o\n", [Round(l[i,3]) : i in [2..#l]];
      result := [<l[i,1], Round(l[i,3])> : i in [2..#l]];
      Bvec := B;
      return;
    end if;
    // find possible extensions
    for j := 1 to #pl do
      if B[j] lt max[j] then
        Bp := B;
        Bp[j] +:= 1;
        if Bp notin reached then
          expsize(~GI, Bp, ~size);
          new := <pl[j], Bp, size>;
          // and update agenda
          Append(~agendas, Append(l, new));
          Append(~agendav, size);
          Include(~reached, Bp);
        end if;
      end if;
    end for;
  end while;
  result := [];
  Bvec := [];
end procedure;

function convertToOldGI(GI, Bvec)
  resGI := [];
  pl := GI`pl;
  for i := 1 to #GI`info do
    relsize(~GI`info[i], pl, Bvec, ~s);
    if s lt 1.0 then
      entry := GI`info[i];
      Append(~resGI, [* entry`p, entry`imbas,
                        ChangeUniverse(entry`imC, Universe(entry`imbas)) *]);
    end if;
  end for;
  return resGI;
end function;

// =========================================================================
// Taken over from previous version:

// Given a set of tuples mod B, return all tuples mod B*p lifting them
// and compatible with GI. Return "primes" used in the process as second
// value.
function LiftInformation(S, GI, B, p)
  // S = {[a1,...,ar], ...} 
  // new version (2008-04-08): split lifting into p-steps
  // preparation: find relevant entries in GI
  vprintf MWSieve, 2: "LiftInformation: B = %o, p = %o, #S = %o\n", B, p, #S;
  r := #GI[1,2];
  vpB := Valuation(B, p);
  Bp := B*p;
  // Select relevant entries from GI
  tests := [e : e in GI | Valuation(Exponent(Universe(e[2])), p) gt vpB];
  // Reduce to the information needed and remove entries that give no
  // restrictions
  tests := [[* e[1], [q(b) : b in e[2]], imC *]
             : e in tests
             | #imC lt #G1
               where imC := {q(c) : c in e[3]}
               where G1, q := quo< G | [Bp*g : g in Generators(G)]>
               where G := Universe(e[2])];
  // Add the homomorphism and their kernels to the data
  MW := FreeAbelianGroup(r);
  tests := [Append(Append(e, h), Kernel(h))
             where h := hom<MW -> Universe(e[2]) | e[2]>
             : e in tests];
  
  // Find a filtration
  //  B*MW = L_0 \supset L_1 \supset ... \supset L_m = B*p*MW
  // such that the expected sizes of the sets of candidates
  //  S_j = {s in MW/L_j : p_ij(h_i(s)) in p_ij(S_i) for all i}
  // where  h_i : MW --> G_i  and  p_ij : G_i -->> G_i/h_i(L_j),
  // are as small as possible.
  // Do it in the greedy way.
  
  // The current subgroup
  BMW := sub<MW | [B*MW.i : i in [1..r]]>;
  // The target subgroup
  BpMW :=  sub<MW | [Bp*MW.i : i in[1..r]]>;
  // The sequence of subgroups, from BMW down to BpMW (initialize)
  steps := [BMW];
  Lcurr := BMW;
  testsleft := tests;
  
  vprintf MWSieve, 2: "  starting computation of steps...\n";
  
  while not IsEmpty(testsleft) do
    vprintf MWSieve, 3: "   Size of testleft: %o\n", #testsleft;
    Lset := {@ Parent(BMW) | @}; // indexed set of subgroups considered
    Lval := [];   // parallel sequence of "values" of these subgroups
    for e in testsleft do
      Lnew := Lcurr meet e[5]; // e[5] = ker(h : MW -> G_e)
      G := Universe(e[2]);
      h := e[4];
      G1, q := quo<G | h(Lcurr)>;
      pd := #G/#G1;
      val := 1.0*#e[3]/#{q(c) : c in e[3]}/pd;
      vprintf MWSieve, 3: "      q = %o, dim = %o, val = %o -- ",
                          e[1], Valuation(pd, p), ChangePrecision(pd*val, 4);
      // try to find Lnew in Lset
      pos := Position(Lset, Lnew);
      if pos eq 0 then
        // not yet in: add it and initialize the value
        vprintf MWSieve, 3: "new subgroup\n";
        Include(~Lset, Lnew);
        Append(~Lval, pd*val);
      else
        // already there: update the value
        Lval[pos] *:= val;
        vprintf MWSieve, 3: "known subgroup, new value = %o\n",
                            ChangePrecision(Lval[pos], 4);
      end if;
    end for; // e in testsleft
    // Find best new subgroup
    m, pos := Min(Lval);
    vprintf MWSieve, 2: "    expected relative growth: %o, dimension: %o\n",
                        ChangePrecision(1.0*m, 5), 
                        Valuation(#quo<Lcurr | Lset[pos]>, p);
    // and put it into the list
    Append(~steps, Lset[pos]);
    Lcurr := Lset[pos];
    // Remove entries that no longer can give information
    testsleft := [e : e in tests | #e[4](Lcurr) gt 1];
  end while;
  
  if Lcurr ne BpMW then
    vprintf MWSieve, 2: "    'Information dimension' is only %o\n",
                        r - Valuation(#quo<Lcurr | BpMW>, p);
  end if;
  vprintf MWSieve, 2: "  starting the lifting...\n";
  vprintf MWSieve, 2: "    intermediate sizes:";
  
  maxsize := 0;
  // now lift S successively
  primes := {};
  Q1, q1 := quo<MW | BMW>;
  S1 := {q1(MW!s) : s in S};
  for j := 2 to #steps do
    L := steps[j];
    QL, qL := quo<MW | L>;
    // first determine relevant elements of tests
    tests1 := [[* e[1], [q(b) : b in e[2]], {q(c) : c in e[3]},
                  hom<QL -> QG | [q(h(g @@ qL)) : g in OrderedGenerators(QL)]> 
               *]
               where QG, q := quo<G | GL>
                : e in tests
                | GL ne h(steps[j-1])
                  where GL := h(L)
                  where h := hom<MW -> G | e[2]>
                  where G := Universe(e[2])];
    // now lift
    hL := hom<QL -> Q1 | [q1(l @@ qL) : l in OrderedGenerators(QL)]>;
    KhL := Set(Kernel(hL));
    cands := {};
    // for each possible lift of an element of S1 to QL,
    //  check if it "survives" all the conditions in tests1
    for a in S1 do
      lifta := qL(a @@ q1); // some lift of a to QL
      for k in KhL do
        // all lifts are obtained by adding elements from the kernel
        c := lifta + k;
        if forall(e){e : e in tests1 | e[4](c) in e[3]} then
          // we have to keep this candidate
          Include(~cands, c);
        else
          // we can discard it. 
          // Note in primes that we have used this entry.
          Include(~primes, e[1]);
        end if;
      end for; // k
    end for; // a
    vprintf MWSieve, 2: " %o", #cands;
    maxsize := Max(maxsize, #cands);
    S1 := cands;
    Q1 := QL;
    q1 := qL;
  end for; // j
  // lift all the way and convert back to sequences
  if Lcurr ne BpMW then
    last, qlast := quo<MW | BpMW>;
    hlast := hom<last -> Q1 | [q1(l @@ qlast) : l in OrderedGenerators(last)]>;
    Klast := Set(Kernel(hlast));
    cands := {(a @@ hlast) + k : k in Klast, a in S1};
    maxsize := Max(maxsize, #cands);
    vprintf MWSieve, 2: " %o", #cands;
  end if;
  S := {Eltseq(c) : c in cands};
  if IsVerbose("MWSieve", 2) then
    if not IsEmpty(primes) then
      printf "\n  entries used: %o", primes;
    end if;
    printf "\n  size of conditions mod %o is %o\n", Bp, #S;
  end if;
  return S, primes, maxsize;
end function;

function BMCompute(GI, run)
  if not IsEmpty(run) and Type(run[1]) eq RngIntElt then
    run := [<r, -1.0> : r in run];
  end if;
  maxsize := 1;
  // initialize
  B := 1;
  r := #GI[1,2];
  cands := {[0 : i in [1..r]]};
  primes := {};
  s := #run;
  for j := 1 to #run do
    p := run[j,1];
    cands, pr, ms := LiftInformation(cands, GI, B, p);
    primes join:= pr;
    maxsize := Max(maxsize, ms);
    B *:= p;
    if IsVerbose("MWSieve", 2) then
      if run[j,2] lt 0 then
        printf "BMCompute: B = %o, size = %o\n", B, #cands;
      else
        printf "BMCompute: B = %o, size = %o (predicted: %o)\n",
               B, #cands, Round(run[j,2]);
      end if;
    end if;
    if IsEmpty(cands) then
      if IsVerbose("MWSieve", 1) then
        printf "SUCCESS with B = %o = %o\n", B, Factorization(B);
        printf "Successive prime factors: %o\n", [run[i,1] : i in [1..j]];
        printf "Primes used: %o\n\n", primes;
      end if;
      s := j;
      break;
    end if;
  end for;
  return [Integers() | run[i,1] : i in [1..s]], cands, primes, maxsize;
end function;

// =========================================================================

procedure CheckPoints1(gens, ls, deg3, ~hp, ~info, ~flag, ~point)
  // Checks if ls[1]*gens[1] + ... gives
  // a point on J that is of the form pt + can - deg3.
  // Returns true and the point pt on the curve or false.
  // hp is the height pairing matrix of gens
  // info[1] = [..., p, ...]
  // info[2] = [* ..., f mod p, ... *]
  // info[3] = [* ..., [gens mod p], ...*]
  // info[4] = [* ..., deg3 mod p, ... *]
  J := Universe(gens);
  prec := 0.0;
  p := 101;
  if not assigned info then
    info := <[Integers()|], [* *], [* *], [* *]>;
  end if;
  if not assigned hp then
    hp := HeightPairingMatrix(gens);
  end if;
  // a rough height bound
  ht1 := (v*hp, v) + 5.0 where v := Vector(RealField(), ls);
  f := PolynomialRing(Integers())!HyperellipticPolynomials(Curve(J));
  disc := Discriminant(f);
  while prec lt ht1 do
    if not IsDivisibleBy(disc, p) then
      pos := Position(info[1], p);
      if pos eq 0 then
        Jp := BaseChange(J, GF(p)); 
        gensp := [Jp!g : g in gens];
        d3p := Dred(f, deg3, p);
        fp := PolynomialRing(GF(p))!f;
        Append(~info[1], p);
        Append(~info[2], fp);
        Append(~info[3], gensp);
        Append(~info[4], d3p);
      else
        fp := info[2][pos];
        gensp := info[3][pos];
        d3p := info[4][pos];
      end if;
      ptJ := TDK(fp, d3p, ls, gensp);
      if ptJ[4] ne 0 then
        // not on curve
        flag := false;
        return;
      end if;
      prec +:= Log(p);
    end if;
    p := NextPrime(p);
  end while;
  // Now there should be a point; find it!
  pt := TDK(f, deg3, ls, gens);
  if pt[4] ne 0 then
    // not on curve
    flag := false;
  else
    C := Curve(J);
    flag := true;
    if pt[3] eq 0 then
      point := Rep(PointsAtInfinity(C));
    else
      point := Rep(Points(C, -pt[2]/pt[3]));
    end if;
  end if;
  return;
end procedure;


// =========================================================================
// Main function

// Do a Mordell-Weil sieve computation in order to show that the curve of J 
// (must be of genus 2, defined over Q and of the form y^2 = f(x)) has no 
// rational points. bas is a sequence of generators of the Mordell-Weil group,
// deg3 specifies an embedding of the curve into J:
//  deg3 is a polynomial b(x) such that  f(x) - b(x)^2 has a factor of odd degree. 
// SmoothBound influences the selection of primes.
//
// Returns:
// 1. true or false, according to whether there is a rational point or not
// 2. a point on the curve (if true) or _ (if false)
// 3. the "q sequence" of successive prime factors of N
// 4. the set of prime (powers) used for local information
// 5. timing and space information

intrinsic HasPointMWSieve(J::JacHyp, bas::[JacHypPt], deg3::RngUPolElt
                            : SmoothBound := 200, testfun := func<p, v | IsOdd(v)>,
                              eps := 0.01, eps1 := 0.1, CheckSmall := true)
                           -> BoolElt, PtHyp, SeqEnum, SetEnum, SeqEnum
{Do a Mordell-Weil sieve computation in order to find out if the curve of J
(must be of genus 2, defined over Q and of the form y^2 = f(x)) has any
rational points.
bas is a sequence of generators of the Mordell-Weil group,
deg3 is a polynomial b(x) such that  f(x) - b(x)^2 has a factor of odd degree.
SmoothBound, testfun, eps and eps1 are technical parameters. If CheckSmall
is true, the function searches for small points on the curve first.
The first return value is true or false. If true, the second reeturn value
is a rational point on the curve. Further return values have a more technical
meaning.}
  t0 := Cputime();
  t1 := 0.0;
  t2 := 0.0;
  t3 := 0.0;
  C := Curve(J);
  require Genus(C) eq 2: "J must be a genus 2 Jacobian.";
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "Curve must be of the form y^2 = f(x).";
  fd3 := Factorization(f - deg3^2);
  degs := [Degree(a[1]) : a in fd3];
  if degs[1] eq 1 then
    // found a rational point
    return true, Rep(Points(C, Roots(fd3[1,1])[1,1])), _, _, _;
  end if;
  if CheckSmall then
    // check for small points
    pts := Points(C : Bound := 1000);
    if not IsEmpty(pts) then
      return true, Rep(pts), _, _, _;
    end if;
  end if;
  pos := Position(degs, 3);
  require pos gt 0: "deg3 must give rise to a rational divisor of degree 3.";
  deg3 := <fd3[pos,1], deg3, 3>;
  vprintf MWSieve, 1: "MWSieve: f = %o, rank = %o\n", f, #bas;
  // construct GI object
  GI := initGI(J, bas, deg3, SmoothBound);
  deg3 := GI`deg3;;
  repeat
    tt := Cputime();
    vprintf MWSieve, 1: " Computing GroupInfo...\n";
    computeGI(~GI, eps, ~short, testfun);
    t1a := Cputime(tt); t1 +:= t1a;
    vprintf MWSieve, 1: "  Time: %o s\n", t1a;
    if short ne 0 then
      vprintf MWSieve, 1: " Contradiction at p = %o\n", short;
      vprintf MWSieve, 1: " Total time: %o s\n", Cputime(t0);
      return false, _, [], {short}, [Cputime(t0), t1, 0.0, 0.0, 0];
    end if;
    tt := Cputime();
    vprintf MWSieve, 1: " Computing q sequence...\n";
    findQSeq(~GI, eps1, ~qseq, ~Bvec);
    t2a := Cputime(tt); t2 +:= t2a;
    vprintf MWSieve, 1: "  Time: %o s\n", t2a;
    tt := Cputime();
    vprintf MWSieve, 1: " Starting sieve computation...\n";
    run1, cands, primes, maxsize := BMCompute(convertToOldGI(GI, Bvec), qseq);
    t3a := Cputime(tt); t3 +:= t3a;
    vprintf MWSieve, 1: "  Size of largest intermediate candidate set: %o\n", maxsize;
    vprintf MWSieve, 1: "  Time: %o s\n", t3a;
    if IsEmpty(cands) then
      t := Cputime(t0);
      vprintf MWSieve, 1: " Total time: %o s\n", t;
      return false, _, run1, primes, [t, t1, t2, t3, maxsize];
    end if;
    // now try to find a point
    B := &*[(GI`pl[i])^Bvec[i] : i in [1..#GI`pl]];
    vprintf MWSieve, 1: " No contradiction yet. Checking for points...\n";
    for c in cands do
      // find shortest representative of candidate
      ls := [2*a gt B select a-B else a : a in c];
      CheckPoints1(bas, ls, deg3, ~hp, ~info, ~flag, ~point);
      if flag then
        vprintf MWSieve, 1: " Point %o found!\n", point;
        t := Cputime(t0);
        vprintf MWSieve, 1: " Total time: %o s\n", t;
        return true, point, _, _, [t, t1, t2, t3, maxsize];
      end if;
    end for;
    // reduce eps and eps1 so that we will use more information in the next
    // pass through the loop
    eps *:= 0.1;
    eps1 *:= 0.1;
  until false;
end intrinsic;

