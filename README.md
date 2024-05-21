# quadratic-torsion

Code to compute the torsion subgroups that occur over a fixed quadratic field. This accompanies the paper [Torsion subgroups of elliptic curves over quadratic fields and a conjecture of Granville](https://arxiv.org/abs/2401.14514).

The paper itself explains what parts of this repo are used where. Here we give an overview of the repo according to each folder.

## computations

This contains the meat of our code. Computing positive rank twists is done in the ipython file `positive_rank_twists.ipynb`. The code for curves $X_1(13)$ and $X_1(18)$ are found in `x1_13.m` (respectively, `x1_18.m`); this is relevant to Section 3. The file `x1_16_chabauty.m` is the main file for running code related to $X_1(16)$ relevant for Section 4. The abc triples are computed in `x1_16_abc_triples.m`, relevant for Section 5.

## genus_one_lists

Contains text files for which quadratic fields the five genus 1 torsion subgroups arise. Relevant to Section 2 of the paper.

## granville_constants

Contains code to compute the constants of Granville in Section 5.

## graphs

Contains the graphs - as well as the code to produce them - shown in Section 5.

## magma_scripts

Contains the code for running the Mordell-Weil sieve on $X_1(13)$ and $X_1(18)$, used in Section 4.

## quadratic_torsion

Contains the code to compute positive rank twists of the modular curves we consider, via the twisted winding element method. This is imported into other files when needed, and is used throughout.

## Project layout

```
.
├── computations
├── genus_one_lists
├── granville_constants
├── graphs
├── magma_scripts
├── quadratic_torsion
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