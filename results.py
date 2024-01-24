
import pandas as pd
%matplotlib inline
import matplotlib
import matplotlib.pyplot as plt


matplotlib.use('gtk3agg')

from matplotlib.ticker import MaxNLocator

# Elliptic lists; these can be generated with 
# quadratic_torsion/positive_rank_twists.py


G_11 = [-9, -7, -4, 5, 7]

G_14 = [-8, -3, 6]

G_15 = [-7, -2, 7, 8]

G_2_10 = [-18, -12, -3, 2, 6, 12]

G_2_12 = [-17, 19]

# Genus 2 lists

G_13 = [17, 113, 193, 313, 481, 1153, 1417, 2257, 3769, 3961, 5449, 6217, 6641, 9881]

G_18 = [33, 337, 457, 1009, 1993, 2833, 7369, 8241, 9049]

G_16 = [ -8030, -8022, -7990, -7462, -6970, -6110, -5106, -3966, -3927, -3255, -3066, -2405, -2030, -1326, -1271, -671, -455, -290, -119, -15, 1, 
10, 15, 41, 51, 70, 93, 105, 205, 217, 391, 546, 609, 679, 1105, 1326, 1378, 1785, 1830, 2370, 3145, 3289, 3585, 3705, 4505, 4522, 4745, 
4945, 5565, 5865, 5890, 6355, 8169, 8570, 9334 ]

# Next make a df out of these lists. First create the zero dataframe

B = 20

# df_index = [d for d in range(-B,B) if ZZ(d).is_squarefree() and d != 1 ]

df_index = range(-B,B)

cols_list = ['Z/11Z', 'Z/14Z', 'Z/15Z', 'Z/2Z + Z/10Z', 'Z/2Z + Z/12Z']

df = pd.DataFrame(0, index=df_index, columns=cols_list)

list_of_cols = [(G_11,'Z/11Z'), (G_14,'Z/14Z'), (G_15,'Z/15Z'), (G_2_10,'Z/2Z + Z/10Z'), (G_2_12,'Z/2Z + Z/12Z')]

for data,label in list_of_cols:
    for i in data:
        df.at[int(i),label] = 1

df = df.astype(float)
ax = df.plot.bar(stacked=True)

ax.set_xlabel('d')
ax.set_ylabel('Frequency of extra quadratic torsion')
ax.yaxis.set_major_locator(MaxNLocator(integer=True))
ax.set_title('Distribution of extra quadratic torsion')
fig = ax.get_figure()
fig.savefig('quadratic-torsion/quadratic_torsion_distribution.png')