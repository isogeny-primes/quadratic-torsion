//Z/16Z
S:=[10, 15, 41, 51, 70, 93, 105, 205, 217, 218, 298, 362, 391, 395];
//No extra points for: 218, 298, 362
_<x>:=PolynomialRing(Rationals());
J:=JOne(16);
L:=LSeries(J);
IsZeroAt(L,1);     // this is false iff rank(J_1(16)(Q))=0
tr, p:=NewModularHyperellipticCurve(ModularSymbols(J));
C1:=HyperellipticCurve(p);

C:=HyperellipticCurve(x*(x^2+1)*(x^2+2*x-1));
J1:=Jacobian(C);
TorsionSubgroup(J1);
Points(J1:Bound:=100);
nrQ := #Points(C:Bound:=1000);
M_2 := ModularSymbols(Gamma1(16));
S_2 := CuspidalSubspace(M_2);
phi := RationalMapping(S_2);

positive_rank := [];
rank_problems := [];
big_rank_problems := [];
for d in S do
    printf "d=%o\n", d;
    C2:=QuadraticTwist(C,d);
    J2:=Jacobian(C2);
    r1, r2:=RankBounds(J2);
    K := QuadraticField(d);
    if r1 ne r2 then
        Append(~rank_problems,d);
        printf "problems %o %o\n", r1, r2;
        C3:=ChangeRing(C,K);
        nrK := #Points(C3:Bound:=1000);
	    //assert nrK eq nrQ;
	end if;
    chi := KroneckerCharacter(d,Rationals());
    w := phi(TwistedWindingElement(S_2,1,chi));
	if w eq 0 then
        print "big problem" , r1, r2;
        print Points(C2:Bound:=10000);
        Append(~big_rank_problems,d);
    else
       points := Chabauty0(J2);
       print points;
    end if;
end for;

print big_rank_problems;
B := 10;
time MW2, mMW2, fl1, fl2 := MordellWeilGroupGenus2(J2 : SearchBounds2 := [B*100, B*200, B*500, B*1000]);

phi := Automorphisms(C2)[3];

p1 := mMW2(MW2.3);
p2 := Pullback(phi, p1);
p3 := mMW2(MW2.4);
t1 :=  mMW2(MW2.1);
t2 :=  mMW2(MW2.2);
p2+t1+t2 eq p3;


bound := 20;
for a1 in [0,1] do
for a2 in [0,1] do
for a3 in [-bound..bound] do
for a4 in [0..bound] do
  if a3^2 + a4^2 gt bound^2 then continue; end if;
  a := [a1,a2,a3,a4];
  pt := mMW2(MW2 ! a);
  if pt[3] lt 2 then;
    print pt;
  end if;
end for;
end for;
end for;
end for;

/*
[ (x^2 + 454471/85776620*x + 5313025/4288831, 2339938973743/359747144280*x +
    300807213725/17987357214, 2), (x^2 - 454471/106260500*x + 4288831/5313025,
    59637231995017/4408748145000*x - 1144688828237/220437407250, 2) ]
*/
/*
for p in  PrimesUpTo(100) do
  time sat, info := Saturation([p1,p2],p);
  print p, info;
  assert sat eq [p1, p2];
end for;
*/