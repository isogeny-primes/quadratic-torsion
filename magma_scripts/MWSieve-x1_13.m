Attach("MWSieve-new.m");
//SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...
R<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);
J:=Jacobian(C);
SetClassGroupBounds("GRH");

OurDsToCheck := [ 673, 1609, 1921, 2089, 2161, 8473, 8641, 9689 ];

function doOurMWSieve(d)

    C1:=QuadraticTwist(C,d);
    f1,_ := HyperellipticPolynomials(C1);
    J1:=Jacobian(C1); // this has rank 2

    G,b,_:=AutomorphismGroup(C1);

    anOrder3Aut := [g : g in G | Order(g) eq 3][1];
    assert Order(anOrder3Aut) eq 3;

    Cquot, mymap := CurveQuotient(AutomorphismGroup(C1,[b(anOrder3Aut)]));

    somePts := Points(Cquot : Bound := 1000);

    aRatPt := somePts[1];

    deg3Divisor:=Pullback(mymap,Place(aRatPt));
    assert Degree(deg3Divisor) eq 3;

    deg3DivisorSupport := Support(deg3Divisor)[1]; // throw away multiplicity
    deg3PseudoPoly := RepresentativePoint(deg3DivisorSupport)[2];  // this is actually an element of a number field, we need the poly, so go through some hassle to get it
    K := Parent(deg3PseudoPoly);

    phi := hom<K -> R | [R.1]>;
    deg3 := phi(deg3PseudoPoly);  // this is now a valid poly which we will now check

    fd3 := Factorization(f1 - deg3^2);
    degs := [Degree(a[1]) : a in fd3];
    bools := [IsOdd(x) : x in degs];
    assert true in bools;

    MW, MWtoSet, flag1, flag2, bound := MordellWeilGroupGenus2(
                                        J1 : 
                                        Rankbound := 2,
                                        SearchBounds := [1000,2000,5000,10000, 50000],
                                        SearchBounds2 := [1000,2000,5000,10000, 50000],
                                        SearchBounds3 := [200,500,1000,2000, 10000],
                                        MaxBound := 50000
    );

    print "flag 1 and flag2 for d = ", d, " are respectively", flag1, "and", flag2;
    if not flag1 then
        return "MW computation failed";
    end if;

    bas := [J1!(MWtoSet(MW.1)), J1!(MWtoSet(MW.2))];

    ans := HasPointMWSieve(J1, bas, deg3: testfun := func<p, v | IsOdd(v) and p gt 3>);  // this is true or false

    return ans;
end function;

for d in OurDsToCheck do
    print "answer for ", d, " is ", doOurMWSieve(d);
end for;
