# Import necessary libraries
import numpy as np
import matplotlib
import matplotlib.pyplot as plt
from collections import Counter

# Function to prepare data for plotting
def points_to_plot(d_list):
    # Copy the list and take absolute values of all elements
    my_d_list = [abs(x) for x in d_list.copy()]
    # Count the occurrences of each value
    counts = dict(Counter(my_d_list))
    # Convert the dictionary to a list of tuples and sort it
    my_d_list = sorted([(k,v) for k,v in counts.items()])
    # Prepare the output list
    i = 0
    output = []
    for x,f in my_d_list:
        i += f
        output.append((x,i))
    # Return the output list with an additional point at the origin
    return [(0,0)]+output

# Create a figure with two subplots
fig, ax = plt.subplots(1,2,figsize=(12, 8))

# Set labels for the axes of the first subplot
ax[0].set_xlabel('B')
ax[0].set_ylabel('T_B(N)')
# Set labels for the axes of the second subplot
ax[1].set_xlabel('B')
ax[1].set_ylabel('T_B(N)')

# Define data sets
G_13 = [17, 113, 193, 313, 481, 1153, 1417, 2257, 3769, 3961, 5449, 6217, 6641, 9881]
G_18 = [33, 337, 457, 1009, 1993, 2833, 7369, 8241, 9049]
G_16 = [ -8030, -8022, -7990, -7462, -6970, -6110, -5106, -3966, -3927, -3255, -3066, -2405, -2030, -1326, -1271, -671, -455, -290, -119, -15, 1, 
10, 15, 41, 51, 70, 93, 105, 205, 217, 391, 546, 609, 679, 1105, 1326, 1378, 1785, 1830, 2370, 3145, 3289, 3585, 3705, 4505, 4522, 4745, 
4945, 5565, 5865, 5890, 6355, 8169, 8570, 9334 ]

# Prepare data for plotting
points_to_plot_13 = points_to_plot(G_13)
points_to_plot_18 = points_to_plot(G_18)
points_to_plot_16 = points_to_plot(G_16)

# Define constants for the fitted curves
KAPPA_13 = 0.65
KAPPA_18 = 0.4  
KAPPA_16 = 2.5

# Generate x values and corresponding y values for the fitted curves
x = np.linspace(0,10000,1000)
y_13 = KAPPA_13 * np.cbrt(x)
y_18 = KAPPA_18 * np.cbrt(x)
y_16 = KAPPA_16 * np.cbrt(x)

# Plot the data and the fitted curves for N = 13 and 18
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

# Plot the data and the fitted curve for N = 16
ax = plt.subplot(1, 2, 2)
ax.set_title("N = 16")
ax.set_xlabel('B')
ax.set_ylabel('T_B(16)')
plt.plot(*zip(*points_to_plot_16), 'or')
plt.plot(*zip(*points_to_plot_16), '-', color="orange", label="N=16")
plt.plot(x, y_16, 'g-', label="fitted-16")
plt.legend(loc="lower right")

# Save the figure
plt.savefig('granville_distribution_fitted.png', dpi=400)