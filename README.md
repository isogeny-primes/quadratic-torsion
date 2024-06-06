# quadratic-torsion

Code to compute the torsion subgroups that occur over a fixed quadratic field. This accompanies the
paper [Torsion subgroups of elliptic curves over quadratic fields and a conjecture of Granville](https://arxiv.org/abs/2401.14514).

The paper itself explains what parts of this repo are used where. Here we give an overview of the repo according to each
folder.

## python_scripts

This directory constains a singele file [positive_rank_twists.py](python_scripts/positive_rank_twists.py). The code in
this file uses SageMath's modular symbol methods to compute which twists of the relavant modular curves have positive
analytic rank. The output of these computations are automatically written to the
[positive_rank_lists folder](#positiveranklists). To reproduce these computations simply do:

```commandline
cd python_scripts
sage positive_rank_twists.py 
```

this computation should take between 1 to 2 days. After the above computations finished the commands

```commandline
cd positive_rank_lists
git diff .
```

can be used to check if the output of the run is the same as the output we obtained initially. `git diff .` will
show any changes in the output. So if that command doesn't print anything then the computations were succesfully
reproduced.

## magma_scripts

This contains the meat of our code. Most of the computations here rely on the results of the output of
`positive_rank_twists.py` in the [pyhton_scrips](#pythonscripts) directory, since as discribed in the paper we only
need to consider the twist of positive algebraic rank. Since algebraic rank > 0 implies analytic rank > 0 we
restrict all computations to the twists in the [positive_rank_lists folder](#positiveranklists).

To reproduce the computations in the file `example.m` this directore either do

```commandline
cd magma_scripts
magma example.m
```

or copy paste the contents of `example.m` into an interactive Magma session.

### The genus 1 modular curves

For the 5 genus 1 modular curves, we only need to verify that the curves that have positive analytic rank also have
positive algebraic rank as predicted by the BSD conjecture. The code for this is in
[positive_rank_twists.m](magma_scripts/positive_rank_twists.m).

### X_1(13) and X_1(18)

For these two modular curves we first do a two descent and a point search. These code for these computations can be
found in [x1_13.m](magma_scripts/x1_13.m) and [x1_18.m](magma_scripts/x1_18.m). These computations should finish in
several minutes, and deal with all but a few cases. For the remaining case we use the mordell weil sieve the code for
this is in [MWSieve-x1_13.m](magma_scripts/MWSieve-x1_13.m) and [MWSieve-x1_18.m](magma_scripts/MWSieve-x1_18.m). These
computations should finish in about a week. Most of the time here is actually spend in searching for generators of the
Mordell-Weil group. And the cases we cannot deal with are because we were unable to find these generators despite the
fact that BSD predicts they should exist.

The verification of the torsion computations of Lemma's 3.3, 3.5 and 4.1 can be found in
[torsionVerifications.m](magma_scripts/torsionVerifications.m). These computations should be finished within a minute.

### X_1(16)

For $X_1(16)$ we do a point search which can be found in [x1_16_point_search.m](magma_scripts/x1_16_point_search.m).
This computation should be done in under a minute. We also combine two cover descent together with elliptic curve
chabauty in order to determine all points in the relevant twists in [x1_16_chabauty.m](magma_scripts/x1_16_chabauty.m).
This computation should finish in 1 to 2 hours.

Additionally, Granville's work on points on twists of genus 2 curves predicts that one should be able to produce
abc-triples form the j-invariants of small points on quadratic twists of $X_1(16)$. The code to compute these triples
can be found in [x1_16_abc_triples.m](magma_scripts/x1_16_abc_triples.m) and the list of triples themselves can be found
in [x1_16_abc_triples_list.txt](logs/x1_16_abc_triples_list.txt). These computations should be finished within a minute.

## granville

Contains code to compute the constants of Granville in Section 5. It also contains the graphs - as well as the code to
produce them - that compare our computations to Granville's conjecture.

## positive_rank_lists

For each of the genus 1 and 2 curves this lists which twists have postive analytic rank. For the five genus 1 curves we
have also verfied that these actually have postive algebraic rank as expected. From this one can directly deduce over
which quadratic fields these five genus 1 modular curves have extra points, as described in section 2 of the paper.

## logs

These contains log files of several magma sessions. These can be used to check if the results from the
[magma_scripts](#magmascripts) agree with the results we obtained when we originally ran these computations.

## Project layout

```
.
├── granville
├── logs
├── magma_scripts
├── positive_rank_lists
├── python_scripts
```

# Copyright

```
####  Copyright (C) 2024 Barinder S. Banwait and Maarten Derickx

Quadratic Torsion is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.

The authors can be reached at: barinder.s.banwait@gmail.com and
maarten@mderickx.nl.
```

