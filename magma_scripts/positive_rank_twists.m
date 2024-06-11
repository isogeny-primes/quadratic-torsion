// This is the Magma implementation of the sage code in quadratic_torsion/positive_rank_twists.py
// Since it is about 8 times slower than the sage code, we do the computation there.
// The code here can be used to verify the sage implementation. However, this code is
// not needed to reproduce the results of our paper.

function IsZeroRankofTwist(G,d)
// This is the Magma implementation of the sage function is_rank_of_twist_zero(G, d) in
//   quadratic_torsion/positive_rank_twists.py
// Since it is about 8 times slower than the sage code, we do this compution in sage.
// And this function is not actually used. However we still include it in case someone
// wants to verify out results using magma.
// it uses modular symbols to compute wether the analytic rank is 0 or not
// if the analytic rank is 0 then the algebraic rank is also guaranteed to be 0
  M := ModularSymbols(G);
  S := CuspidalSubspace(M);
  chi := BaseExtend(KroneckerCharacter(d),RationalField());
  tw := TwistedWindingElement(S,1, chi);
  // print tw;
  twmap := RationalMapping(S)(tw);
  // print twmap;
  return not twmap eq Parent(twmap)!0;
end function;


// For each of the elliptic curves that have positive analytic rank
// we verify that they also have positive algebraic rank.
// It returns true, 0 if all twists of E by the integers d in Dlist indeed have postive
// algberaic rank. And returns false, d whenever there is an integer d such that E
// twisted by d has rank 0.
function VerifyPositiveRank(E, Dlist)
    not_found_list := [];
    error_list := [];
    for d in Dlist do
        Ed := QuadraticTwist(E,d);
        try
            rank := Rank(Ed : Effort := 2);
        catch e
            Append(~error_list, <d, e`Object>);
            continue;
        end try;
        if rank eq 0 then
            Append(~not_found_list, d);
        end if;
    end for;
    return not_found_list, error_list;
end function;


// This is what we run to verify that the algebraic rank of the 
// 5 elliptic modular curves with positive analytic rank is also positive.
// The log of running this is in logs/elliptic_rank_verifs_log.txt

data := [
  <SmallModularCurve(11), "../positive_rank_lists/11_list.json">,
  <SmallModularCurve(14), "../positive_rank_lists/14_list.json">,
  <SmallModularCurve(15), "../positive_rank_lists/15_list.json">,
  <SmallModularCurve(20), "../positive_rank_lists/2_10_list.json">,
  <SmallModularCurve(24), "../positive_rank_lists/2_12_list.json">
];

// Since class group bounds are only ever used for upper bounds,
// and we are only interested in verifying that the rank is positive,
// we can set the class group bounds to assume GRH.
SetClassGroupBounds("GRH");

for Eloc in data do
  E,loc := Explode(Eloc);
  DList := eval Read(loc);
  print VerifyPositiveRank(E, DList);
end for;