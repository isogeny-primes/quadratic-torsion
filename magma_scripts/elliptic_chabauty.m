QQ:=Rationals();
Qx<x> := PolynomialRing(QQ);
P1:=ProjectiveSpace(QQ,1);

function Zip(a, b)
  //similar to pythons zip function
  assert #a eq #b;
  n := #a;
  return [<a[i],b[i]> : i in [1..n]];
end function;

function createHktoA(AtoHk, expvecs, factorbase)
  A := Domain(AtoHk);
  A2 := Parent(factorbase[1]);
  phi := hom< A2 -> A | A.1 >;
  Hk := Domain(expvecs);
  HktoA := map< Hk -> A | h :-> phi(&*[ef[2]^ef[1] : ef in Zip(Eltseq(expvecs(h)),factorbase)])>;
  return HktoA;
end function;




function EllipticChabauty(C, g, hk, HktoA)
  assert BaseRing(C) eq QQ;
  assert Degree(g) in [3,4];
  success := true;
  points := {@ @};
  CtoP1 := map< C -> P1 | [C.1,C.3] >;
  K := BaseRing(g);
  A := Codomain(HktoA);
  f := ChangeRing(Modulus(A), QQ);
  L := quo< Parent(g) | g>;
  assert Evaluate(f, L.1) eq 0;
  AtoL := hom< A -> L | L.1>;

  gamma := Norm(AtoL(HktoA(hk)));

  for p in PrimeDivisors(Numerator(Norm(gamma))) do
    while IsIntegral(gamma/p^2) do
      gamma := gamma/p^2;
    end while;
  end for;
  print "gamma", gamma;

  E := HyperellipticCurve(gamma*g);
  EtoP1:=map<E->P1|[E.1,E.3]>;
  iselliptic, E1raw, EtoE1raw, E1rawtoE := IsEllipticCurve(E);
  if not iselliptic then
    print "finding points";
    time Epoints := Points(E : Bound:=100);
    //print #Epoints;
    if #Epoints eq 0 then
      success := false;
      print "no points found";
      return success, points;
    end if;
    iselliptic := true;
    P0 := Setseq(Epoints)[1];
    E1raw,EtoE1raw:=EllipticCurve(E,P0);
    E1rawtoE := Inverse(EtoE1raw);
  end if;

  //todo make everything work with a minimal model if we can find one
  //this will make computations much faster
  E1 := MinimalModel(E1raw);
  print Factorization(Integers() ! Norm(Discriminant(E1raw)/Discriminant(E1)));
  time MW1, MW1toE1set, flag1, flag2 := MordellWeilGroup(E1);
  success := success and flag1 and flag2;
  if not success then;
    print hk, g, flag1, flag2;
    return success, <"mw failed", flag1, flag2>;
  end if;
  MW1toE1 := map<MW1 -> E1 | x :-> MW1toE1set(x)>;
  //print Invariants(MW1), flag1, flag2;
  E1toE1raw := Isomorphism(E1,E1raw);
  //E1rawtoE1 := Inverse(E1toE1raw);
  E1toE := E1toE1raw*E1rawtoE;
  E1toP1 := Expand(E1toE1raw*E1rawtoE*EtoP1);

  if TorsionFreeRank(MW1) ge Degree(K) then
    print "rank", TorsionFreeRank(MW1);
    success := false;
    return success, [*MW1, MW1toE1, E1, E1toP1*];
  end if;
  pointset := Chabauty(MW1toE1, E1toP1);


  for t in pointset do
    //print Parent(t),t;
    P := E1toE(MW1toE1(t));
    xP := EtoP1(P);
    xP := P1(QQ) ! xP;
    new_points := RationalPoints( xP@@CtoP1 );
    //print t, xP, RationalPoints( xP@@CtoP1 );
    points := points join new_points;
  end for;
  return success, points;
end function;



f1 := -x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := f1*f2*f3;

g1 := -x;
g2 := x^2+1;
g3 := -x^2 - 2*x + 1;
g := g1*g2*g3;
//f := 2*x^6+x^4+3*x^2-2;
failed_list := [];
success_list := [];
extra_point_list := [* *];
positive_rank := [ 10, 15, 41, 51, 70, 79, 93, 94, 105, 141, 143, 159, 182, 187, 205, 217, 222,
246, 274, 303, 310, 313, 319, 345, 366, 370, 391, 394, 395, 406, 409, 411, 415,
435, 442, 510, 535, 542, 546, 598, 609, 634, 671, 679, 697, 751, 761, 782, 794,
809, 889, 939, 949, 959, 969, 1001, 1007, 1039, 1081, 1086, 1105, 1113, 1155,
1186, 1195, 1293, 1302, 1310, 1326, 1334, 1337, 1378, 1426, 1435, 1526, 1533,
1547, 1554, 1561, 1570, 1581, 1626, 1657, 1695, 1705, 1735, 1738, 1759, 1767,
1785, 1786, 1830, 1869, 1897, 1906, 2026, 2067, 2110, 2121, 2193, 2198, 2301,
2329, 2345, 2370, 2395, 2399, 2410, 2415, 2422, 2427, 2454, 2463, 2482, 2526,
2569, 2626, 2665, 2681, 2686, 2706, 2710, 2713, 2730, 2767, 2773, 2794, 2905,
2953, 2985, 2986, 2990, 3003, 3031, 3055, 3085, 3094, 3122, 3129, 3145, 3215,
3289, 3354, 3374, 3570, 3585, 3615, 3657, 3689, 3705, 3791, 3805, 3895, 3946,
3967, 3970, 4010, 4029, 4079, 4123, 4278, 4310, 4345, 4381, 4393, 4395, 4441,
4498, 4505, 4506, 4522, 4633, 4745, 4754, 4758, 4771, 4795, 4810, 4921, 4943,
4945 ];
for N in positive_rank do
  if N lt 1000 then continue; end if;
  print(Seqset(failed_list));
  print "=============================== doing:", N, " ======================";

  if not IsSquarefree(N) then continue; end if;

  C := HyperellipticCurve(N*f);
  C1 := HyperellipticCurve(N*g);
  time Hk , AtoHk, expvecs, factorbase := TwoCoverDescent(C: PrimeBound:=30, Raw:=true);
  HktoA := createHktoA(AtoHk, expvecs, factorbase);

  K2 := NumberField(f2);
  f2a := Factorization(ChangeRing(f2, K2))[1][1];
  f2E := f3*f2a;
  g2a := Factorization(ChangeRing(g2, K2))[1][1];
  g2E := g3*g2a;

  K3 := NumberField(f3);
  f3a := Factorization(ChangeRing(f3, K3))[1][1];
  f3E := f2*f3a;
  g3a := Factorization(ChangeRing(g3, K3))[1][1];
  g3E := g2*g3a;

  //print "#Hk:", #Hk;
  Hk := Setseq(Hk);
  points := {@ @};
  for i in [1..#Hk] do
    hk := Hk[i];
    //print "doing hk", i, hk;
    assert AtoHk(HktoA(hk)) eq hk;
    success := false;
    for fE in [* f3E, f2E, x*f3E, x*f2E *] do
      success, new_points := EllipticChabauty(C, fE, hk, HktoA);
      print "chabauty result", success, new_points;
      if success then
        points := points join new_points;
        break; 
      end if;
    end for;
    if not success then
      print "=============================== failed ======================";
      print N, hk;
      Append(~failed_list,N);
    end if;
  end for;
  print "points for N:", N, points;
  if success then
    Append(~success_list, N);
    if #points gt 2 then
      Append(~extra_point_list, <N, points>);
      print "====================== extra points!!! ====================";
    end if;
  end if;
end for;

print(Seqset(failed_list));
print(success_list);
print(extra_point_list);





success, points := EllipticChabauty(C, f3E, hk, HktoA);
MW1, MW1toE1, E1, E1toP1 := Explode(points);


B := 40;
for i in [0,1] do
for j in [-B..B] do
for k in [-B..B] do
  mw := i*MW1.1 + j*MW1.2 + k*MW1.3;
  x := E1toP1(MW1toE1(mw));
  if x in P1(QQ) then
    print i,j,k,x;
  end if;
end for;
end for;
end for;

/*
A<theta> := Domain(AtoHk);
deltas:={-1-theta,1-theta};
{AtoHk(d): d in deltas} eq Hk;
{HktoA(h)*d: d in deltas};
{AtoHk(HktoA(h)*d): d in deltas};
*/

RK2<u,v> := PolynomialRing(K2,2);

//g(x) = (x-b0/a0)*(x-b1/a1)= x^2 + k*x + l
//f_b = x^2 + k_b*x + l_b = 0
//f_a = x^2 + k_a*x + l_a = 0
//(a0x-b0)*(a1x-b1)=a0*a1x^2-(a0*b1+a1*b0)x+b0*b1=gamma_g(hk)*g(x)
//u^2=(a0x-b0)*gamma*g
//v^2=(a1x-b1)*gamma*g



//u^2 + v^2 = (-k_a*x+k_b)*g

//(u+v)^2=(-k_a*x+k_b)*g + 2*u*v
//(u*v)^2 = (a0x-b0)*gamma*g*(a1x-b1)*gamma*g=a1*a2*f*(gamma*g)^2

R<uxv,upv,w> := PolynomialRing(QQ,3);
gamma:=1;
k_a := -2;
k_b := 0;
fw := (w^2 - 2*w - 1);
h2 := uxv^2-gamma*(w^2+1)*fw^2;
h3 := upv^2-(-k_a*w+k_b)*fw-2*uxv;
C0 := Curve(AffineSpace(R),[h2,h3]);
Genus(C0);

R<u,v,w> := PolynomialRing(K2,3);
fw := (w^2 - 2*w - 1);
h2 := u^2-(w-K2.1)*fw;
h3 := v^2-(w+K2.1)*fw;

function EllipticCurveGenus2WeilRestriction(f, g, hk, HktoA)
  assert Degree(f) eq 2;
  assert Degree(g) in [2,3];
  assert IsSquarefree(f);
  assert IsSquarefree(g);

  K := NumberField(f);
  A := Codomain(HktoA);
  f_A := ChangeRing(Modulus(A), QQ);
  fac := Factorization(f);
  if #fac eq 1 then
    fac := Factorization(ChangeRing(f,K));
  end if;

  f1 := fac[1][1];
  f2 := fac[2][1];

  cf1 := -ConstantCoefficient(f1);
  cf2 := -ConstantCoefficient(f2);
  assert Evaluate(f_A, cf1) eq 0;
  assert Evaluate(f_A, cf2) eq 0;
  AtoK1 :=  hom< A -> K | cf1>;
  AtoK2 :=  hom< A -> K | cf2>;

  L := quo< Parent(g) | g>;
  assert Evaluate(f_A, L.1) eq 0;
  AtoL := hom< A -> L | L.1>;

  hka := HktoA(hk);
  gamma := Norm(AtoL(hka));
  a1 := AtoK1(hka);
  a2 := AtoK2(hka);
  b1 := cf1*a1;
  b2 := cf2*a2;

  R<uxv,upv,w> := PolynomialRing(QQ,3);

  k_a := QQ ! (-a1-a2);
  l_a := QQ ! (a1*a2);
  k_b := QQ ! (-b1-b2);
  fw := Evaluate(f,w);
  gw := Evaluate(g,w);
  /*
  gamma := 1;
  k_a := -2;
  k_b := 0;
  l_a := 1;
  */
  //h2 := uxv^2-gamma*(w^2+1)*fw^2;
  //h3 := upv^2-(-k_a*w+k_b)*fw-2*uxv;
  h2 := uxv^2-l_a*fw*(gamma*gw)^2;
  h3 := upv^2-(-k_a*w+k_b)*gamma*gw-2*uxv;
  C := Curve(AffineSpace(R),[h2,h3]);
  return C;
end function;

f := f2;
g := f3;
for hk in Hk do
  print "-------------------------------\n";
  C := EllipticCurveGenus2WeilRestriction(f, g, hk, HktoA);
  tf, Ch, CtoCh := IsHyperelliptic(C);
  if tf then
    print Genus(Ch), hk, C,Ch;
  else
    print Genus(C), Image(CanonicalMap(C));
  end if;
  print "rank", RankBounds(Jacobian(Ch));
  mw := MordellWeilGroup(Jacobian(Ch));
  print "rank", mw;
  C := EllipticCurveGenus2WeilRestriction(g, f, hk, HktoA);
  tf, Ch, CtoCh := IsHyperelliptic(C);
  if tf then
    print Genus(Ch), hk, C,Ch;
  else
    print Genus(C), Image(CanonicalMap(C));
  end if;
  print "rank", RankBounds(Jacobian(Ch));
  mw := MordellWeilGroup(Jacobian(Ch));
  print "rank", mw;
end for;

R<u1,u2,v1,v2,w1,w2> := PolynomialRing(K2,6);
h2e := Evaluate(h2,[u1+K2.1*u2,v1+K2.1*v2,w1+K2.1*w2]);
h3e := Evaluate(h2,[u1+K2.1*u2,v1+K2.1*v2,w1+K2.1*w2]);



R<u1,u2,w1,w2> := PolynomialRing(QQ,4);
h2e1 := u1^2 - u2^2 - w1^3 + 2*w1^2 + 3*w1*w2^2 - 2*w1*w2 + w1 - 2*w2^2 + 2*w2;
h2e2 := 2*u1*u2 - 3*w1^2*w2 + w1^2 + 4*w1*w2 - 2*w1 + w2^3 - w2^2 + w2 - 1;
C := Curve(AffineSpace(R), [w2,h2e1,h2e2]);
tf, Ch := IsHyperelliptic(C);
K4 :=  NumberField(Factorization(HyperellipticPolynomials(Ch))[2][1]);

//h3e1 := u1^2 - u2^2 - w1^3 + 2*w1^2 + 3*w1*w2^2 - 2*w1*w2 + w1 - 2*w2^2 + 2*w2;
//h3e2 := 2*u1*u2 - 3*w1^2*w2 + w1^2 + 4*w1*w2 - 2*w1 + w2^3 - w2^2 + w2 - 1;

//Q[w]  -> K1[w]
//Res L/Q A1_K (A1_Q) = A1_K(A1_K)
// P1_Q -> Res L/Q P1_K = A1_K -> A1_K
// Q[w] <- Q[w1,w2] = K[w] <- K[w]
C := Curve(AffineSpace(R),[h2,h3]);
Genus(C);
Can := map< C -> Curve(ProjectiveSpace(K2,1)) | DefiningEquations(CanonicalMap(C))>;
C := Curve(RamificationDivisor(Can));
Can := map< C -> Curve(ProjectiveSpace(K2,1)) | DefiningEquations(CanonicalMap(C))>;
ram := RamificationDivisor(Can);
ram2 := Pushforward(Can,ram);
I :=  Ideal(ram2);
R<x,y> := Parent(I.1);
print I;
Evaluate(Basis(I)[1],[x,1]);
R<x> := PolynomialRing(K2,1);
Factorization(x^6 - x^4 - K2.1*x^2 + K2.1);
R<x> := PolynomialRing(QQ,1);
R<u,v,w> := PolynomialRing(K2,3);
fw := (w^2 - 2*w - 1);
h2 := u^2-(w-K2.1)*fw;
h3 := v^2-(w+K2.1)*fw;
h4 := u^2*v^2 - (w+K2.1)*fw*(w-K2.1)*fw;
C := Curve(AffineSpace(R),[h4, h2+h3]);
Genus(C);

R<u,v,w> := PolynomialRing(QQ,3);
h23 := u^2 + v^2 - 2*w^3 + 4*w^2 + 2*w;
h4 := u^2*v^2 - w^6 + 4*w^5 - 3*w^4 - 3*w^2 - 4*w - 1;
C := Curve(AffineSpace(R),[h4, h23]);
Genus(C);


R<u,v,w> := PolynomialRing(QQ,3);
fw := (w^2 + 1);
h2 := u^2-(w^2 - 2*w - 1)*fw;
h3 := v^2-(2*w+2)*fw-2*u;
C := Curve(AffineSpace(R),[h2,h3]);
Genus(C);

R<y,u,v,w> := PolynomialRing(QQ,4);
h1 := y^2-(w^2 - 2*w - 1);
//h1 := y-(w^2 - 2*w - 1);
h2 := u^2-(w^2+1);
h3 := v^2-2*u;
Genus(Curve(AffineSpace(R),[h1,h2,h3]));

Rx<x> := PolynomialRing(K2);
R<u,v,w> := PolynomialRing(K2,3);
p1 := 1000000007;
p2 := 10000000019;
fw := w*(w-1);
h2 := u^2-(w-p1)*fw;
h3 := v^2-(w-p2)*fw;
C := Curve(AffineSpace(R),[h2,h3]);
print Genus(C);
tf, Ch, CtoCh := IsHyperelliptic(C);
f1, f2, f3 := Explode(DefiningEquations(CtoCh));
assert f1 eq u*v;
assert f2 eq (-81000000216000000144/500000006500000021)*w^3*(w-1)^3*u*(w - 1000000007);
assert f3 eq (w-1000000007)*fw;

u2 := (w-p1)*fw;
v2 := (w-p2)*fw;


map< C -> Ch | [v,(-2*(p2-p1)^2/p1/(p1-1))*w^2*(w-1)^2,u]>;
map< C -> Ch | [v*u,(-2*(p2-p1)^2/p1/(p1-1))*w^2*(w-1)^2*u^3,u^2]>;

f := (p2-p1)*(x^2-1)*(p2*x^2-p1)*((p2-1)*x^2-(p1-1));
Ch2 := HyperellipticCurve(f);
map< C -> Ch2 | [u, ((p2-p1)*fw)^2, v]>;

R<u,v,w,p1,p2,a0,a1,a2,a3> := PolynomialRing(QQ,9);
Rx<x> := PolynomialRing(R);
p1 := 1; p2 := 0;
fw := w*(w-1);
u2 := (w-p1)*fw;
v2 := (w-p2)*fw;
(u2-v2) eq (p2-p1)*fw;
(p2*u2-p1*v2) eq w*(p2-p1)*fw;
((p2-1)*u2-(p1-1)*v2) eq (w-1)*(p2-p1)*fw;
(p2-p1)*(u2-v2)*(p2*u2-p1*v2)*((p2-1)*u2-(p1-1)*v2) eq ((p2-p1)*fw)^4;
m := Matrix([
  [1, -2*p1 , p1^2 ],
  [1, -2*p2 , p2^2 ],
  [1, -p1-p2, p1*p2]
]);

m2 := Matrix([
  [p2^2, p1^2, -2*p1*p2],
  [p2  , p1  , -(p1+p2)],
  [1   , 1   , -2      ]
]);
(1/(p1-p2)^2)*(m*m2);


m := Matrix([
  [-p1^3, 3*p1^2, -3*p1, 1],
  [-p1^2*p2, p1^2 + 2*p1*p2, -2*p1 - p2, 1],
  [-p1*p2^2, 2*p1*p2 + p2^2, -p1 - 2*p2, 1],
  [-p2^3, 3*p2^2, -3*p2, 1]
]);
m2 := ((1/a1*(a1*m))^-1);
print (p1-p2)^3*m2;
//m*[1, w, w^2, w^3]=[u2^3, u2^2*v2, u2*v2^2, v2^3];
//[1, w, w^2, w^3] = m2*[u2^3, u2^2*v2, u2*v2^2, v2^3]
u2 := (w-p1);
v2 := (w-p2);

vec := Transpose(Matrix([[1/p1*(p1*u2^3), u2^2*v2, u2*v2^2, v2^3]]));
print m2*vec;
print  Numerator((Vector([a0/a0*a0,a1,a2,a3])*m2*vec)[1]);
R<p1,p2> := PolynomialRing(QQ,2);
Rx<x> := PolynomialRing(R);
f := (p2-p1)*(x^2-1)*(p2*x^2-p1)*((p2-1)*x^2-(p1-1));
f0 := (x^2-1)*(p2*x^2-p1)*((p2-1)*x^2-(p1-1));
C0 := HyperellipticCurve(f0);
A3 := AffineSpace(QQ,3);
A2 := AffineSpace(R);
invs := G2Invariants(C0);
K<u,v> := Parent(invs[1]);
[Evaluate(invs[i],[v,u]) eq invs[i] : i in [1,2,3]];
invs := IgusaInvariants(C0);
K<u,v> := Parent(invs[1]);
[Evaluate(invs[i],[v,u]) eq invs[i] : i in [1..5]];
[Factorization(Denominator(invs[i])) : i in [1,2,3,5]];

R<a0,a1,a2,a3> := PolynomialRing(QQ,4);
Rx<x> := PolynomialRing(R);
f00 := a3*x^6+a2*x^4+a1*x^2+a0;
C00 := HyperellipticCurve(f00);
A3<x1,x2,x3> := AffineSpace(QQ,3);
A4 := AffineSpace(R);
invs := G2Invariants(C00);
phi := map< A4->A3 | invs>;
X := Image(phi);
f :=  DefiningEquation(X);