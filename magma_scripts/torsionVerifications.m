/*
    Here we verify Lemma 3.3
*/

R<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);

for p in [5,17] do
   print p , Invariants(ClassGroup(ChangeRing(C, GF(p^2))));
end for;

J:=Jacobian(C);
TorsionSubgroup(J);

/*
    Here we verify Lemma 3.5
*/

f := R![1, 2, 5, 10, 10, 4, 1];
C:=HyperellipticCurve(f);
J:=Jacobian(C);

for p in PrimesInInterval(5,17) do
   print p , Invariants(ClassGroup(ChangeRing(C, GF(p^2))));
end for;

J:=Jacobian(C);
TorsionSubgroup(J);

/*
    Here we verify Lemma 4.1
*/

f := R![1, -4, 4, 4, -12, 8];
C:=HyperellipticCurve(f);
J:=Jacobian(C);

for p in PrimesInInterval(3,17) do
   print p , Invariants(ClassGroup(ChangeRing(C, GF(p^2))));
end for;

J:=Jacobian(C);
TorsionSubgroup(J);
