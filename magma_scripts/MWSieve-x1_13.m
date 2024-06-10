/*
    This carries out the MW sieve on the `unsolved` list of twists of X1(13)
*/

// Load the MW sieve implementation of Bruin and Stoll
Attach("MWSieve-new.m");
//SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...

// Define the curve and Jacobian
R<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);
J:=Jacobian(C);

// The list of ds that we haven't solved with other methods.
OurDsToCheck := [ 673, 1609, 1921, 2089, 2161, 8473, 8641, 9689 ];
// Uncomment the following line to speed up the verification. This skips the case 9689 that we know will fail anyway.
// OurDsToCheck := [ 673, 1609, 1921, 2089, 2161, 8473, 8641 ];

// We know the analytic rank is positive for all these modular curves.
// We verify that the algebraic rank is at most 2 for all these modular curves
// Since then later for the Mordell-Weil sieving to return the correct answer
// it suffices to find the saturation of two independent generators.
rank_le_2 := [];
rank_unknown := [];
for d in OurDsToCheck do
  C1:=QuadraticTwist(C,d);
  J := Jacobian(C1);
  b1, b2 := RankBounds(J);
  if b2 eq 2 then
    Append(~rank_le_2, d);
  else
    Append(~rank_unknown, d);
  end if;
end for;
print(rank_le_2);
print(rank_unknown);
assert #rank_unknown eq 0;

// Make the code run faster
// We can now safely use GRH since the only place GRH for better class group bounds is
// used is in proving rank upper bounds in the MordellWeilGroupGenus2 function.

SetClassGroupBounds("GRH");

// Define the function that does the MW sieve
function MWSieve(d)

    // Define the twist
    C1:=QuadraticTwist(C,d);
    f1,_ := HyperellipticPolynomials(C1);
    J1:=Jacobian(C1); // this has rank 2

    // As explained in the paper, the implementaiton requires a 
    // degree 3 divisor. Obtaining this is done as follows

    // First compute the automorphism group

    G,b,_:=AutomorphismGroup(C1);

    // Next find an automorphism of order 3

    anOrder3Aut := [g : g in G | Order(g) eq 3][1];
    assert Order(anOrder3Aut) eq 3;

    // Next compute the quotient curve

    Cquot, mymap := CurveQuotient(AutomorphismGroup(C1,[b(anOrder3Aut)]));

    // Find a rational point on the quotient curve

    somePts := Points(Cquot : Bound := 1000);
    aRatPt := somePts[1];

    // Pull back the rational point to a divisor on the curve
    deg3Divisor:=Pullback(mymap,Place(aRatPt));
    assert Degree(deg3Divisor) eq 3; // Woo hoo!

    deg3DivisorSupport := Support(deg3Divisor)[1]; // throw away multiplicity
    deg3PseudoPoly := RepresentativePoint(deg3DivisorSupport)[2];

    // this is actually an element of a number field, we need the poly,
    // so go through some hassle to get it
    K := Parent(deg3PseudoPoly);

    phi := hom<K -> R | [R.1]>;
    deg3 := phi(deg3PseudoPoly);  // this is now a valid poly which we will now sanity check as follows

    fd3 := Factorization(f1 - deg3^2);
    degs := [Degree(a[1]) : a in fd3];
    bools := [IsOdd(x) : x in degs];
    assert true in bools;  // so it is a valid input for the Bruin-Stoll Mordell-Weil sieve

    // That was computing the deg3 divisor. Now we proceed with getting generators of the MW group

    // do the mw group computation with increasing search bounds in order to speed up the computation

    SearchBounds := [1000,2000,5000,10000, 50000];
    SearchBounds2 := [1000,2000,5000,10000, 50000];
    SearchBounds3 := [200,500,1000,2000, 10000];

    for i in [1..#SearchBounds] do

      print "doing MW computation for d = ", d, "bound index i = ", i;
      MW, MWtoSet, flag1, flag2, bound := MordellWeilGroupGenus2(
                                            J1 :
                                            Rankbound := 2,
                                            SearchBounds := [SearchBounds[i]],
                                            SearchBounds2 := [SearchBounds2[i]],
                                            SearchBounds3 := [SearchBounds3[i]],
                                            MaxBound := SearchBounds[i]
      );
      if flag1 and flag2 then break; end if;
    end for;


    // Check the computation actually worked, and if not, return that we failed

    print "flag 1 and flag2 for d = ", d, " are respectively", flag1, "and", flag2;
    if not (flag1 and flag2)  then
        success := false;
        points := [];
        return success, points, "MW computation failed";
    end if;

    // the correctness of the code below asummes that the MW group is isomorphic to
    // Z x Z, so we assert that this is indeed the case.
    assert Invariants(MW) eq [0,0];

    // The desired basis
    bas := [J1!(MWtoSet(MW.1)), J1!(MWtoSet(MW.2))];

    // Here we do the MW sieve
    has_point, point := HasPointMWSieve(J1, bas, deg3: testfun := func<p, v | IsOdd(v) and p gt 3>);  // has_point is true or false

    success := true;
    if has_point then
        return success, [point], "found a point";
    else
        return success, [], "the curve has no points";
    end if;
end function;

// Run it for the d we need to check
unsolved := [];
has_point := [];
has_no_point := [];
for d in OurDsToCheck do
    success, points, message := MWSieve(d);
    print "answer for ", d, " is ", message;
    if success then
       if #points eq 0 then
         Append(~has_no_point, d);
       else
         Append(~has_point, d);
       end if;
    else
       Append(~unsolved, d);
    end if;
end for;

print unsolved;
print has_point;
print has_no_point;
