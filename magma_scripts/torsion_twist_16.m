//Z/16Z
_<x>:=PolynomialRing(Rationals());
J:=JOne(16);
tr, p:=NewModularHyperellipticCurve(ModularSymbols(J));
C1:=HyperellipticCurve(p);

C:=HyperellipticCurve(x*(x^2+1)*(x^2+2*x-1));
// so C is a model for X_1(16)
assert IsIsomorphic(C, C1);

for p in PrimesInInterval(3,7) do
  print p , Invariants(ClassGroup(ChangeRing(C, GF(p^2))));
end for;
// this shows that the torsion subgroup over a quadratic field is always a subgroup of
// Z/2Z x Z/2Z x Z/2Z x Z/10Z
// according to https://www.lmfdb.org/Genus2Curve/Q/256/a/512/1 the Q rational torsion is
// Z/2Z x Z/10Z
// so only the 2 torsion can grow over quadratic fields.
// However, all the 2 torsion is rational over the splitting field of
// x*(x^2+1)*(x^2+2*x-1)
// This field is Q(i, \sqrt{2})  so torsion can only grow over Q(i) and Q(\sqrt{+/-2})
// todo compute the 2 torsion over these 3 fields, this should be possible with pure
// thought since se can read of the galois representation of Q(i, \sqrt{2})
// on the roots from the equation above.
