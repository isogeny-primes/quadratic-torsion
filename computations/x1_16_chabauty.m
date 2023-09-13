QQ := Rationals();
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
  assert IsMonic(g);
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
  gamma_g := <gamma,g>;

  E := HyperellipticCurve(gamma*g);
  EtoP1:=map<E->P1|[E.1,E.3]>;
  iselliptic, E1raw, EtoE1raw, E1rawtoE := IsEllipticCurve(E);
  if not iselliptic then
    print "finding points";
    time Epoints := Points(E : Bound:=100);

    if #Epoints eq 0 then
      success := false;
      return success, gamma_g, points, "point search failed";
    end if;
    iselliptic := true;
    P0 := Setseq(Epoints)[1];
    E1raw,EtoE1raw:=EllipticCurve(E,P0);
    E1rawtoE := Inverse(EtoE1raw);
  end if;

  E1 := MinimalModel(E1raw);


  success,MW1, MW1toE1set:=PseudoMordellWeilGroup(E1);
  if not success then;

    r := Degree(K);

    return success, gamma, points, <"mw failed",Invariants(MW1), r>;
  end if;
  MW1toE1 := map<MW1 -> E1 | x :-> MW1toE1set(x)>;

  E1toE1raw := Isomorphism(E1,E1raw);

  E1toE := E1toE1raw*E1rawtoE;
  E1toP1 := Expand(E1toE1raw*E1rawtoE*EtoP1);

  if TorsionFreeRank(MW1) ge Degree(K) then
    success := false;
    return success, gamma_g, points, <"rank to large",TorsionFreeRank(MW1),Degree(K)>;
  end if;

  pointset, R := Chabauty(MW1toE1, E1toP1: IndexBound:=2);
  print R, #pointset;
  assert IsPowerOf(R,2);

  for t in pointset do

    P := E1toE(MW1toE1(t));
    xP := EtoP1(P);
    xP := P1(QQ) ! xP;
    new_points := RationalPoints( xP@@CtoP1 );
    points := points join new_points;
  end for;


  return success, gamma_g, points, "found all points";
end function;



f1 := x;
f2 := x^2+1;
f3 := x^2 - 2*x - 1;
f := -f1*f2*f3;

K2 := NumberField(f2);
f2a := Factorization(ChangeRing(f2, K2))[1][1];

K3 := NumberField(f3);
f3a := Factorization(ChangeRing(f3, K3))[1][1];


K4 := CyclotomicField(8);
f2b := Factorization(ChangeRing(f2, K4))[1][1];
f3b := Factorization(ChangeRing(f3, K4))[1][1];

failed_list := [];
failed_info := AssociativeArray();
success_list := [];
extra_points := AssociativeArray();
// for some reason the computation either hangs or takes very long for these values
skip := {-1271, -119, 51};

// positive rank under BSD in range [-10000,10000]
todo_list := [-9995, -9959, -9910, -9906, -9899, -9887, -9886, -9830, -9754, -9743, -9690, -9618, -9590, -9530, -9487, -9458, -9389, -9366, -9355, -9290, -9289, -9282, -9271, -9231, -9215, -9210, -9051, -9030, -9022, -8989, -8943, -8927, -8879, -8786, -8690, -8687, -8651, -8617, -8610, -8538, -8527, -8502, -8479, -8421, -8366, -8365, -8346, -8319, -8259, -8255, -8251, -8186, -8143, -8126, -8098, -8058, -8043, -8030, -8022, -7990, -7973, -7946, -7919, -7887, -7871, -7854, -7826, -7797, -7727, -7711, -7710, -7635, -7622, -7615, -7567, -7505, -7503, -7462, -7455, -7431, -7421, -7359, -7279, -7197, -7161, -7034, -7006, -6970, -6969, -6942, -6790, -6774, -6767, -6758, -6711, -6639, -6630, -6603, -6594, -6503, -6466, -6465, -6347, -6305, -6251, -6239, -6169, -6162, -6149, -6110, -6095, -6063, -6046, -6041, -6031, -6010, -6005, -5951, -5834, -5830, -5829, -5754, -5734, -5678, -5593, -5570, -5567, -5565, -5554, -5546, -5519, -5469, -5406, -5385, -5334, -5330, -5295, -5293, -5289, -5253, -5177, -5138, -5135, -5106, -5090, -5071, -5061, -5019, -4991, -4970, -4911, -4862, -4847, -4826, -4774, -4773, -4754, -4745, -4703, -4674, -4607, -4559, -4539, -4479, -4454, -4447, -4415, -4395, -4386, -4371, -4346, -4286, -4271, -4254, -4233, -4227, -4207, -4191, -4186, -4159, -4134, -4074, -4029, -4011, -3994, -3966, -3927, -3926, -3903, -3901, -3805, -3794, -3766, -3755, -3730, -3723, -3705, -3689, -3657, -3638, -3615, -3614, -3570, -3553, -3503, -3439, -3433, -3410, -3346, -3255, -3237, -3215, -3206, -3199, -3165, -3162, -3135, -3126, -3111, -3106, -3066, -3055, -3003, -3002, -2993, -2990, -2938, -2921, -2905, -2886, -2874, -2847, -2845, -2815, -2810, -2806, -2765, -2706, -2681, -2679, -2665, -2607, -2603, -2534, -2482, -2447, -2415, -2405, -2399, -2378, -2329, -2319, -2302, -2297, -2290, -2285, -2255, -2183, -2159, -2138, -2135, -2121, -2090, -2078, -2071, -2030, -2010, -1999, -1995, -1959, -1906, -1887, -1871, -1869, -1823, -1810, -1786, -1778, -1749, -1739, -1730, -1695, -1673, -1662, -1635, -1626, -1581, -1565, -1515, -1505, -1435, -1390, -1343, -1338, -1330, -1326, -1279, -1271, -1247, -1190, -1189, -1186, -1165, -1022, -1007, -1001, -959, -958, -939, -935, -926, -881, -871, -815, -799, -795, -779, -767, -761, -751, -734, -713, -697, -671, -623, -615, -590, -518, -511, -510, -479, -474, -455, -447, -446, -434, -431, -429, -415, -395, -365, -346, -345, -341, -319, -314, -313, -303, -290, -282, -271, -254, -246, -239, -230, -205, -190, -159, -143, -127, -122, -119, -105, -102, -79, -74, -47, -41, -26, -15, 1, 10, 15, 41, 51, 70, 79, 93, 94, 105, 141, 143, 159, 182, 187, 205, 217, 222, 246, 274, 303, 310, 313, 319, 345, 366, 370, 391, 394, 395, 406, 409, 411, 415, 435, 442, 510, 535, 542, 546, 598, 609, 634, 671, 679, 697, 751, 761, 782, 794, 809, 889, 939, 949, 959, 969, 1001, 1007, 1039, 1081, 1086, 1105, 1113, 1155, 1186, 1195, 1293, 1302, 1310, 1326, 1334, 1337, 1378, 1426, 1435, 1526, 1533, 1547, 1554, 1561, 1570, 1581, 1626, 1657, 1695, 1705, 1735, 1738, 1759, 1767, 1785, 1786, 1830, 1869, 1897, 1906, 2026, 2067, 2110, 2121, 2193, 2198, 2301, 2329, 2345, 2370, 2395, 2399, 2410, 2415, 2422, 2427, 2454, 2463, 2482, 2526, 2569, 2626, 2665, 2681, 2686, 2706, 2710, 2713, 2730, 2767, 2773, 2794, 2905, 2953, 2985, 2986, 2990, 3003, 3031, 3055, 3085, 3094, 3122, 3129, 3145, 3215, 3289, 3354, 3374, 3570, 3585, 3615, 3657, 3689, 3705, 3791, 3805, 3895, 3946, 3967, 3970, 4010, 4029, 4079, 4123, 4278, 4310, 4345, 4381, 4393, 4395, 4441, 4498, 4505, 4506, 4522, 4633, 4745, 4754, 4758, 4771, 4795, 4810, 4921, 4943, 4945, 5066, 5071, 5111, 5122, 5135, 5167, 5185, 5257, 5293, 5330, 5334, 5385, 5395, 5430, 5565, 5593, 5649, 5681, 5754, 5842, 5865, 5890, 5945, 5974, 5995, 6031, 6073, 6157, 6162, 6233, 6235, 6239, 6271, 6355, 6365, 6486, 6559, 6602, 6666, 6683, 6774, 6902, 6953, 6969, 7003, 7006, 7049, 7106, 7161, 7189, 7193, 7210, 7221, 7261, 7339, 7341, 7378, 7379, 7455, 7519, 7561, 7567, 7574, 7582, 7609, 7674, 7705, 7711, 7733, 7786, 7871, 7878, 7922, 7954, 8030, 8062, 8074, 8130, 8131, 8155, 8169, 8189, 8246, 8255, 8286, 8295, 8365, 8395, 8459, 8479, 8565, 8569, 8570, 8574, 8601, 8645, 8690, 8857, 8905, 8906, 8961, 9006, 9034, 9042, 9051, 9062, 9110, 9118, 9194, 9214, 9322, 9334, 9366, 9398, 9553, 9646, 9685, 9709, 9833, 9871, 9961, 9982];
// failed cases
//todo_list := [-8259, -8022, -7973, -7615, -7462, -7161, -7006, -6711, -6503, -6095, -6031, -6005, -5106, -4911, -4847, -4773, -4674, -4371, -4191, -4074, -3927, -3503, -3199, -2405, -1810, -1749, -815, 205, 217, 969, 1105, 1186, 1378, 3215, 3374, 3585, 3705, 3946, 4633, 4745, 5257, 5385, 5565, 5890, 7006, 7210, 7733, 8459, 8479, 8569, 8570, 9709, 9961 ];
for N in todo_list do
  if N in skip then continue; end if;
  print(Seqset(failed_list));
  print "=============================== doing:", N, " ======================";

  if not IsSquarefree(N) then continue; end if;

  C := HyperellipticCurve(N*f);

  time Hk , AtoHk, expvecs, factorbase := TwoCoverDescent(C: Raw:=true);
  HktoA := createHktoA(AtoHk, expvecs, factorbase);

  Hk := Setseq(Hk);
  points := {@ @};
  hk_info := [* *];
  for i in [1..#Hk] do
    hk := Hk[i];
    //print "doing hk", i, hk;
    assert AtoHk(HktoA(hk)) eq hk;
    success := false;
    fE_info := [* *];
    for fE in [* f1*f2, f1*f3, f2*f3, f2a*f3, f3a*f2, x*f2a*f3, x*f3a*f2, x*f2b*f3b *] do
      print "======== doing f =====", fE;
      success, gamma_g, new_points, message := EllipticChabauty(C, fE, hk, HktoA);
      print "chabauty result", success, gamma_g, new_points, message;
      Append(~fE_info, <gamma_g,message>);
      if success then
        points := points join new_points;
        break;
      end if;
    end for;
    Append(~hk_info,fE_info);
    if not success then
      print "=============================== failed ======================";
      print N, hk, i, #Hk;
      Append(~failed_list,N);
      failed_info[N] := hk_info;
      break;
    end if;
  end for;
  if success then
    Append(~success_list, N);
  end if;
  if #points gt 2 then
    extra_points[N] := points;
    print "====================== extra points!!! ====================";
  end if;
  print "points for N:", N, points;
end for;

print(Seqset(failed_list));
print(success_list);
print(extra_points);
print(failed_info);
print(skip);