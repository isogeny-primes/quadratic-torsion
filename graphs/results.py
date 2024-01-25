import numpy as np
import matplotlib
import matplotlib.pyplot as plt
from collections import Counter


def points_to_plot(d_list):
    my_d_list = d_list.copy()
    my_d_list = [abs(x) for x in my_d_list]
    counts = dict(Counter(my_d_list))
    my_d_list = [(k,v) for k,v in dict(counts).items()]
    my_d_list.sort()
    i = 0
    output = []
    for x,f in my_d_list:
        i += f
        output.append((x,i))
        # output.append((x,i / float(x)**(1.0/3.0)))
    return [(0,0)]+output

fig, ax = plt.subplots(1,2,figsize=(12, 8))

ax[0].set_xlabel('B')
ax[0].set_ylabel('T_B(N)')
ax[1].set_xlabel('B')
ax[1].set_ylabel('T_B(N)')


G_13 = [17, 113, 193, 313, 481, 1153, 1417, 2257, 3769, 3961, 5449, 6217, 6641, 9881]
G_18 = [33, 337, 457, 1009, 1993, 2833, 7369, 8241, 9049]

G_16 = [ -8030, -8022, -7990, -7462, -6970, -6110, -5106, -3966, -3927, -3255, -3066, -2405, -2030, -1326, -1271, -671, -455, -290, -119, -15, 1, 
10, 15, 41, 51, 70, 93, 105, 205, 217, 391, 546, 609, 679, 1105, 1326, 1378, 1785, 1830, 2370, 3145, 3289, 3585, 3705, 4505, 4522, 4745, 
4945, 5565, 5865, 5890, 6355, 8169, 8570, 9334 ]

points_to_plot_13 = points_to_plot(G_13)
points_to_plot_18 = points_to_plot(G_18)
points_to_plot_16 = points_to_plot(G_16)

# KAPPA_13 = 1.65  # 2.535 times too big
# KAPPA_18 = 1.50  # 5000, 7  # 3.75 times too big
# KAPPA_16 = 12.4  # 20000, 9  # 5 times too big

KAPPA_13 = 0.65
KAPPA_18 = 0.4  
KAPPA_16 = 2.5

x = np.linspace(0,10000,1000)

y_13 = KAPPA_13 * np.cbrt(x)
y_18 = KAPPA_18 * np.cbrt(x)
y_16 = KAPPA_16 * np.cbrt(x)

ax = plt.subplot(1, 2, 1)
ax.set_title("N = 13 and 18")
ax.set_xlabel('B')
ax.set_ylabel('T_B(N)')


plt.plot(*zip(*points_to_plot_13), 'or')
plt.plot(*zip(*points_to_plot_13), 'r-', label="N=13")

plt.plot(*zip(*points_to_plot_18), 'or')
plt.plot(*zip(*points_to_plot_18), 'b-', label="N=18")

plt.plot(x, y_13, 'g-', label="fitted-13")
plt.plot(x, y_18, 'm-', label="fitted-18")
plt.legend(loc="upper left")

ax = plt.subplot(1, 2, 2)
ax.set_title("N = 16")
ax.set_xlabel('B')
ax.set_ylabel('T_B(16)')

plt.plot(*zip(*points_to_plot_16), 'or')
plt.plot(*zip(*points_to_plot_16), '-', color="orange", label="N=16")

plt.plot(x, y_16, 'g-', label="fitted-16")
plt.legend(loc="lower right")

plt.savefig('granville_distribution_fitted.png', dpi=400)
