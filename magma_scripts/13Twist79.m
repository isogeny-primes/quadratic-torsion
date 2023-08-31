Attach("MWSieve-new.m");
//SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...
R<x>:=PolynomialRing(Rationals());
f := x^6-2*x^5+x^4-2*x^3+6*x^2-4*x+1;
C:=HyperellipticCurve(f);
J:=Jacobian(C);

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


    a,b, flag1, flag2 := MordellWeilGroupGenus2(J1);
    assert flag1 and flag2;

    bas := [J1!(b(a.1)), J1!(b(a.2))];

    ans := HasPointMWSieve(J1, bas, deg3: testfun := func<p, v | IsOdd(v) and p gt 3>);  // this is true or false

    return ans;
end function;

for d in OurDsToCheck do
    print "answer for ", d, " is ", doOurMWSieve(d);
end for;

/*

    NETHER REGIONS

a,b,_,_,_ := MordellWeilGroupGenus2(J1);

bas := [J1!(b(a.1)), J1!(b(a.2))];

f1,_ := HyperellipticPolynomials(C1);

deg3 := 1/6*(-673*x^2 + 673*x);  // this is wrong, this doesn't work

Attach("MWSieve-new.m");
SetVerbose("MWSieve", 1); SetVerbose("GroupInfo", 1); // see what happens...

Support(Pullback(mymap, Place(aRatPt)));

// payload

HasPointMWSieve(J1, bas, deg3);  // this fails because deg3 is wrong above

*/

/* 
//bad box search

for a1 in [-30..30] do
    for a2 in [-10..10] do
        for a3 in [-10..10] do
            for a4 in [-5..5] do
                deg3 := (a1/3)*x^3 + (a2/7)*x^2 + a3*x + a4;
                fd3 := Factorization(f1 - test^2);
                degs := [Degree(a[1]) : a in fd3];
                bools := [IsOdd(x) : x in degs];
                if true in bools then
                    print deg3;
                end if;
            end for;
        end for;
    end for;
end for;

for a1 in [-100..100] do
    for a2 in [-100..100] do
        for a3 in [-100..100] do

            deg3 := (a1/4)*x^2 + (a2/2)*x + (a3/1);
            fd3 := Factorization(f1 - deg3^2);
            degs := [Degree(a[1]) : a in fd3];
            bools := [IsOdd(x) : x in degs];
            if true in bools then
                print deg3;
            end if;

        end for;
    end for;
end for;

for phi in a do
    if Order(phi) gt 1 then 
        Cquot, mymap := CurveQuotient(AutomorphismGroup(C1,[b(phi)]));
        conicModel,_ := Conic(Cquot);
        print "ans for quotient by", phi, " is", IsLocallySoluble(conicModel);
    end if;
end for;

*/