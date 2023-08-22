
from collections import defaultdict

def genus(N):
    assert N.ambient_group().exponent() == 2
    assert N.is_abelian()
    n =  N.ambient_group().ngens()
    ramified_points = [False]*n
    g = 0
    for i,v in enumerate(N.gens()):
        ram_deg = 0
        for j,e in enumerate(v.exponents()):
            if e and not ramified_points[j]:
                ramified_points[j] = True
                ram_deg += 2**i
        g = (2*(2*g-2)+ram_deg+2)/2
    ramified_count = sum([1 for x in ramified_points if x])
    assert g == (2**(N.ngens())*(2*0-2)+ramified_count*2**(N.ngens()-1) + 2)/2
    return g

def as_ambient(v):
    one = v.parent().ambient_group()(1)
    return prod([g ** e for g, e in zip(v.parent().gens(), v.exponents())], one)

g = 2
n = 2*g+2
G = AbelianGroup([2]*n)
H = G.subgroup([G.gen(i)/G.gen(0) for i in range(1,n)])
subG = G.subgroups()
subH = [N for N in subG if N.is_subgroup(H)]
N = subH[0]

genera = defaultdict(lambda:0)
groups_by_invs = defaultdict(lambda:[])

for N in subH:
    weights_N = sorted(sum(as_ambient(v).exponents()) for v in N)
    invariants = (N.ngens(), genus(N), tuple(weights_N))
    if not genera[invariants]:
        print(N,invariants)
    genera[invariants] += 1
    groups_by_invs[invariants].append(N)

"""
{(5, 17, (0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 6)): 1, #H
 (4, 5, (0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4)): 6, # binomial(6,5) (1,1,0,0,0,0)+(1,0,1,0,0,0)+(1,0,0,1,0,0)+(1,0,0,0,1,0)
 (4, 9, (0, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 6)): 15, # binomial(6,4) (1,1,0,0,0,0)+(1,0,1,0,0,0)+(1,0,0,1,0,0)+(0,0,0,0,1,1)
 (4, 9, (0, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4)): 10, # binomial(6,3)/2(1,1,0,0,0,0)+(1,0,1,0,0,0)+(0,0,0,1,1,0)+(0,0,0,1,0,1)
 (3, 1, (0, 2, 2, 2, 2, 2, 2, 4)): 15, # binomial(6,4)  (1,1,0,0)+(1,0,1,0)+(1,0,0,1)
 (3, 3, (0, 2, 2, 2, 2, 4, 4, 4)): 60, # binomial(6,3)*binomial(3,2)  (1,1,0,0,0) + (1,0,1,0,0) + (0,0,0,1,1)
 (3, 5, (0, 2, 2, 2, 4, 4, 4, 6)): 35, # (binomial(6,3)) {f0*f2, f1*f2, f0*f1*f2*f3*f4*f5} + binomial(6,4)*binomial(6,4)*binomial(6,4)/6 {f0*f1, f2*f3, f4*f5},
 (3, 5, (0, 2, 2, 4, 4, 4, 4, 4)): 45, # (6*5*4*3)/8 (1,0,1,0,0,0)+(0,1,0,1,0,0)+(0,0,1,1,1,1)
 (2, 0, (0, 2, 2, 2)): 20, # 6*binomial(5,2)/3=binomial(6,3) (1,1,0,0,0,0)+(1,0,1,0,0,0)
 (2, 1, (0, 2, 2, 4)): 45, # binomial(6,2)*binomial(4,2)/2 (1,1,0,0,0,0)+(0,0,1,1,0,0)
 (2, 2, (0, 2, 4, 4)): 60, # binomial(6,2)*binomial(4,3) (1,1,0,0,0,0)+(0,1,1,1,1,0)
 (2, 3, (0, 2, 4, 6)): 15, # binomial(6,2) (1,1,0,0,0,0)+(0,0,1,1,1,1)
 (2, 3, (0, 4, 4, 4)): 15, # binomial(6,4)*binomial(4,2)*binomial(2,2)/6 = (1,1,1,1,0,0) + (1,1,0,0,1,1)
 (1, 0, (0, 2)): 15, # binomial(6,2) (1,1,0,0,0,0)
 (1, 1, (0, 4)): 15, # binomial(6,4) (1,1,1,1,0,0)
 (1, 2, (0, 6)): 1, # binomial(6,6) (1,1,1,1,1,1)
 (0, 0, (0,)): 1} #trivial group
"""

"""
(3, 5, (0, 2, 2, 2, 4, 4, 4, 6)) # 20 {f0*f2, f1*f2, f0*f1*f2*f3*f4*f5} ->
  (2, 0, (0, 2, 2, 2)): 20, 
  # no since 22 form a subgroup (2, 1, (0, 2, 2, 4)): 45,
  (2, 2, (0, 2, 4, 4)): 60,
  (2, 3, (0, 2, 4, 6)): 15,
  # no since 444 doesnt form a subgroup (2, 3, (0, 4, 4, 4)): 15,

(2, 2, (0, 2, 4, 4)): 60,  # binomial(6,2)*binomial(4,3) (1,1,0,0,0,0)+(0,1,1,1,1,0) ->
  (1, 0, (0, 2)): 15, # binomial(6,2) (1,1,0,0,0,0)
  (1, 1, (0, 4)): 15, # binomial(6,4) (1,1,1,1,0,0)
  # no since genus (1, 2, (0, 6)): 1, # binomial(6,6) (1,1,1,1,1,1)

"""
[[1 (trivial_group)
 
 [15 == binomial(6,2) (1,1,...), 15 == binomial(6,4) (1,1,1,1,...), 1  ==binomial(6,6) (1,1,1,1,1,1)],
 
 [20 == 6*binomial(5,2)/3=binomial(6,3) (1,1,0)+(1,0,1), 
  45 == binomial(6,2)*binomial(4,2)/2 (1,1,0,0)+(0,0,1,1)==(0,0,1,1)+(1,1,0,0) ,
  60 == binomial(6,2)*binomial(4,3) (1,1,0,0,0)+(0,1,1,1,1)==(1,1,0,0,0)+(1,0,1,1,1), 
  30 == 15 + 15 == (binomial(6,2) (1,1,0,0,0,0)+(0,0,1,1,1,1)) + (binomial(6,4)*binomial(4,2)*binomial(2,2))/6 = (1,1,1,1,0,0) + (1,1,0,0,1,1)) ],
 
 [0, 
  15 == 6*binomial(5,3)/4  (1,1,0,0)+(1,0,1,0)+(1,0,0,1),
  0, 
  60 == binomial(6,3)*binomial(3,2)  (1,1,0,0,0) + (1,0,1,0,0) + (0,0,1,1,1),
  0,
  80],
 [0, 0, 0, 0, 0, 6, 0, 0, 0, 25, 0, 0, 0, 0, 0, 0, 0, 0],
 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]
"""