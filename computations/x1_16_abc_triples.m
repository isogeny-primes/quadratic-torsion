/*
  This file generates the abc triples according to the ideas in Section 5.1 of the paper.
  The computations in this file depend on mdmagma v0.1.0 which can be found at:

      https://github.com/koffie/mdmagma/releases/tag/v0.1.0

  In order to download the correct version of mdmagma and reproduce the computations here do

        git clone --branch v0.1.0 https://github.com/koffie/mdmagma.git
        cd mdmagma
        magma

  This downloads the correct version of mdmagma and starts a new magma session in which
  the files of mdmagma can easily be loaded. After this just copy paste the contents of
  this file in that magma session.

  If people know of a packaging manager for magma that makes this more elegant please
  open an issue at https://github.com/koffie/mdmagma/issues .

*/

load "X_1_n.m";

positive_rank := [-9995, -9959, -9910, -9906, -9899, -9887, -9886, -9830, -9754, -9743, -9690, -9618, -9590, -9530, -9487, -9458, -9389, -9366, -9355, -9290, -9289, -9282, -9271, -9231, -9215, -9210, -9051, -9030, -9022, -8989, -8943, -8927, -8879, -8786, -8690, -8687, -8651, -8617, -8610, -8538, -8527, -8502, -8479, -8421, -8366, -8365, -8346, -8319, -8259, -8255, -8251, -8186, -8143, -8126, -8098, -8058, -8043, -8030, -8022, -7990, -7973, -7946, -7919, -7887, -7871, -7854, -7826, -7797, -7727, -7711, -7710, -7635, -7622, -7615, -7567, -7505, -7503, -7462, -7455, -7431, -7421, -7359, -7279, -7197, -7161, -7034, -7006, -6970, -6969, -6942, -6790, -6774, -6767, -6758, -6711, -6639, -6630, -6603, -6594, -6503, -6466, -6465, -6347, -6305, -6251, -6239, -6169, -6162, -6149, -6110, -6095, -6063, -6046, -6041, -6031, -6010, -6005, -5951, -5834, -5830, -5829, -5754, -5734, -5678, -5593, -5570, -5567, -5565, -5554, -5546, -5519, -5469, -5406, -5385, -5334, -5330, -5295, -5293, -5289, -5253, -5177, -5138, -5135, -5106, -5090, -5071, -5061, -5019, -4991, -4970, -4911, -4862, -4847, -4826, -4774, -4773, -4754, -4745, -4703, -4674, -4607, -4559, -4539, -4479, -4454, -4447, -4415, -4395, -4386, -4371, -4346, -4286, -4271, -4254, -4233, -4227, -4207, -4191, -4186, -4159, -4134, -4074, -4029, -4011, -3994, -3966, -3927, -3926, -3903, -3901, -3805, -3794, -3766, -3755, -3730, -3723, -3705, -3689, -3657, -3638, -3615, -3614, -3570, -3553, -3503, -3439, -3433, -3410, -3346, -3255, -3237, -3215, -3206, -3199, -3165, -3162, -3135, -3126, -3111, -3106, -3066, -3055, -3003, -3002, -2993, -2990, -2938, -2921, -2905, -2886, -2874, -2847, -2845, -2815, -2810, -2806, -2765, -2706, -2681, -2679, -2665, -2607, -2603, -2534, -2482, -2447, -2415, -2405, -2399, -2378, -2329, -2319, -2302, -2297, -2290, -2285, -2255, -2183, -2159, -2138, -2135, -2121, -2090, -2078, -2071, -2030, -2010, -1999, -1995, -1959, -1906, -1887, -1871, -1869, -1823, -1810, -1786, -1778, -1749, -1739, -1730, -1695, -1673, -1662, -1635, -1626, -1581, -1565, -1515, -1505, -1435, -1390, -1343, -1338, -1330, -1326, -1279, -1271, -1247, -1190, -1189, -1186, -1165, -1022, -1007, -1001, -959, -958, -939, -935, -926, -881, -871, -815, -799, -795, -779, -767, -761, -751, -734, -713, -697, -671, -623, -615, -590, -518, -511, -510, -479, -474, -455, -447, -446, -434, -431, -429, -415, -395, -365, -346, -345, -341, -319, -314, -313, -303, -290, -282, -271, -254, -246, -239, -230, -205, -190, -159, -143, -127, -122, -119, -105, -102, -79, -74, -47, -41, -26, -15, 1, 10, 15, 41, 51, 70, 79, 93, 94, 105, 141, 143, 159, 182, 187, 205, 217, 222, 246, 274, 303, 310, 313, 319, 345, 366, 370, 391, 394, 395, 406, 409, 411, 415, 435, 442, 510, 535, 542, 546, 598, 609, 634, 671, 679, 697, 751, 761, 782, 794, 809, 889, 939, 949, 959, 969, 1001, 1007, 1039, 1081, 1086, 1105, 1113, 1155, 1186, 1195, 1293, 1302, 1310, 1326, 1334, 1337, 1378, 1426, 1435, 1526, 1533, 1547, 1554, 1561, 1570, 1581, 1626, 1657, 1695, 1705, 1735, 1738, 1759, 1767, 1785, 1786, 1830, 1869, 1897, 1906, 2026, 2067, 2110, 2121, 2193, 2198, 2301, 2329, 2345, 2370, 2395, 2399, 2410, 2415, 2422, 2427, 2454, 2463, 2482, 2526, 2569, 2626, 2665, 2681, 2686, 2706, 2710, 2713, 2730, 2767, 2773, 2794, 2905, 2953, 2985, 2986, 2990, 3003, 3031, 3055, 3085, 3094, 3122, 3129, 3145, 3215, 3289, 3354, 3374, 3570, 3585, 3615, 3657, 3689, 3705, 3791, 3805, 3895, 3946, 3967, 3970, 4010, 4029, 4079, 4123, 4278, 4310, 4345, 4381, 4393, 4395, 4441, 4498, 4505, 4506, 4522, 4633, 4745, 4754, 4758, 4771, 4795, 4810, 4921, 4943, 4945, 5066, 5071, 5111, 5122, 5135, 5167, 5185, 5257, 5293, 5330, 5334, 5385, 5395, 5430, 5565, 5593, 5649, 5681, 5754, 5842, 5865, 5890, 5945, 5974, 5995, 6031, 6073, 6157, 6162, 6233, 6235, 6239, 6271, 6355, 6365, 6486, 6559, 6602, 6666, 6683, 6774, 6902, 6953, 6969, 7003, 7006, 7049, 7106, 7161, 7189, 7193, 7210, 7221, 7261, 7339, 7341, 7378, 7379, 7455, 7519, 7561, 7567, 7574, 7582, 7609, 7674, 7705, 7711, 7733, 7786, 7871, 7878, 7922, 7954, 8030, 8062, 8074, 8130, 8131, 8155, 8169, 8189, 8246, 8255, 8286, 8295, 8365, 8395, 8459, 8479, 8565, 8569, 8570, 8574, 8601, 8645, 8690, 8857, 8905, 8906, 8961, 9006, 9034, 9042, 9051, 9062, 9110, 9118, 9194, 9214, 9322, 9334, 9366, 9398, 9553, 9646, 9685, 9709, 9833, 9871, 9961, 9982];


load "X_1_n.m"; //this file can be found at https://github.com/koffie/mdmagma

// Here we define X1(16) as in other parts of the repo
R<x> := PolynomialRing(Rationals());
f := x*(x^2+1)*(x^2+2*x-1);
C := HyperellipticCurve(f);

// This instantiates X1(16) from the mdmagma package, that comes equipped with
// lots of other useful functions, in particular j-maps
X := X_1_n(16,Rationals());
_,_,_,_,b,c,_,_:= Functions_xyrsbcF2F3(X);
Euniv := EllipticCurve([1-c,-b,-b,0,0]);
jX := jInvariant(Euniv);
isIso,phi := IsIsomorphic(C,X);
jC := Pullback(phi,jX); // this is the j-line

S0<x0,y0> := Parent(Numerator(jC));

R<y,x> := PolynomialRing(Rationals(),2);
S := quo< R | y^2 - x*(x^2+1)*(x^2+2*x-1)>;
h := hom< S0 -> S | x,y >;
//h is just to get different lex ordering so only x remains as variable

// Here is the numerator of the j-map expressed in x only
h(Numerator(jC));

// This will up to gcd's and a factor of 1728 be the c of the abc triple later
R<x> := PolynomialRing(Rationals());
c := -x^48 + 24*x^46 + 492*x^44 - 13336*x^42 - 73602*x^40 + 2509320*x^38 +
    1587516*x^36 - 171403272*x^34 + 315735825*x^32 + 2624226160*x^30 -
    1232025384*x^28 - 19630993776*x^26 - 32538576668*x^24 - 19630993776*x^22 -
    1232025384*x^20 + 2624226160*x^18 + 315735825*x^16 - 171403272*x^14 +
    1587516*x^12 + 2509320*x^10 - 73602*x^8 - 13336*x^6 + 492*x^4 + 24*x^2 - 1;

assert c eq (x^16 - 8*x^14 - 228*x^12 + 968*x^10 + 2630*x^8 + 968*x^6 - 228*x^4 - 8*x^2 + 1)^3;
assert h(Numerator(jC)) eq Evaluate(c, S.2);

// Here is the denominator of the j-map expressed in x only
h(Denominator(jC));

// This will up to gcd's and a factor of 1728 be the a of the abc triple later
a := (x^44 - 20*x^42 + 174*x^40 - 884*x^38 + 2925*x^36 - 6544*x^34 + 9640*x^32 -
    7632*x^30 - 2158*x^28 + 15080*x^26 - 21164*x^24 + 15080*x^22 - 2158*x^20 -
    7632*x^18 + 9640*x^16 - 6544*x^14 + 2925*x^12 - 884*x^10 + 174*x^8 - 20*x^6
    + x^4) * 1728;

assert a eq x^4 * (x - 1)^16 * (x + 1)^16 * (x^2 - 2*x - 1) * (x^2 + 2*x - 1) * (x^2 + 1)^2 * 1728;

// For an abc triple we have a + b = c
b := c - a;

// This function takes input a rational point P on a twist of X1(16), and returns 
// j(P)/1728
function j1728_from_point(point);
    x_p := point[1]/point[3];
    j1728 := Evaluate(c,x_p)/Evaluate(a,x_p);
    return j1728;
end function;

// This function takes input a rational point P on a twist of X1(16), and returns 
// the corresponding abc triple, as described in Section 5.1 of the paper
function abc_from_point(point);
    j1728 := j1728_from_point(point);
    x_c := Numerator(j1728);
    x_a := Denominator(j1728);
    x_b := Abs(x_c-x_a);
    x_c := Abs(x_c);
    x_a := Abs(x_a);
    x_a, x_c := Explode([Min([x_a,x_b,x_c]),Max([x_a,x_b,x_c])]);
    x_b := x_c-x_a;
    return [x_a,x_b,x_c];
end function;

// The rest of this file just runs the above function on lots of twists and outputs
// to screen; see the log file for the output
extra_point_ds := [];
extra_point_abcs := AssociativeArray();

_<x>:=PolynomialRing(Rationals());
for d in positive_rank do
  C:=HyperellipticCurve(d*x*(x^2+1)*(x^2+2*x-1));
  points := Points(C: Bound:=10000);
  if #points gt 2 then
    print "====", d, #points, "====";
    print points;

    // we remove some degenerate cases from the list of points that
    // do not actually yield an abc triple. As the equations at the beginning of
    // section 4 show, these points such that x = point[1]/point[3] is either 0,1,-1
    // or infinity, which are all cusps. These have j=infinity and hence do not yield
    // abc triples.
    points := {point : point in points | point[1] ne 0 and
                                         point[3] ne 0 and
                                         point[1]/point[3] ne 1 and
                                         point[1]/point[3] ne -1};


    js := {j1728_from_point(point) : point in points};
    print js;
    abc := {abc_from_point(point) : point in points};
    extra_point_abcs[d] := Sort(Setseq(abc));
    Append(~extra_point_ds, d);
  end if;

end for;

function abc_info(abc, d)
  // compute the factorization and the quality of the abc triple so that we can easily
  // print the info on the different abc triples we found
  factorization := [Factorization(i): i in abc];
  radical := &*[p[1] : p in F, F in factorization];
  c := Max(abc);
  quality := Log(c)/Log(radical);
  return <quality, d, factorization, abc>;
end function;

// uncomment the following if you want output that can be easily parsed by
// https://github.com/koffie/abc-triples
// print([[[[d]],abcs]: d -> abcs in extra_point_abcs]);

/*
  the format is

   <quality, d, [
        Factorization(a),
        Factorization(b),
        Factorization(c)
    ], [ a,
    b,
    c]>
*/
print(Sort([abc_info(abc, d): d -> abc in abcs, abcs in extra_point_abcs]));
