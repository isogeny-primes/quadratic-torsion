import json

from sage.all import ModularSymbols, kronecker_character, is_squarefree, Gamma0, Gamma1


def is_rank_of_twist_zero(G, d):
    """
    Let J(G) denote the jabobian of the modular curve X(G).
    This function decides wether the quadratic of the jacobian J(G) by d has
    analytic rank 0 or not.

    :param G: A congruence subgroup intermediate between Gamma0 and Gamma1
    :param d: an integer
    :return: true if the analytic rank is 0 and False otherwise
    """
    M = ModularSymbols(G)
    S = M.cuspidal_subspace()
    phi = S.rational_period_mapping()
    chi = kronecker_character(d)
    w = phi(M.twisted_winding_element(0, chi))
    return w != 0


def positive_rank_twists_in_range(G, start, stop):
    """
    Let J(G) denote the jabobian of the modular curve X(G).
    This function computes the list of squarefree integers d between start and stop
    such that twist of J(G) by d has positive analytic rank.

    :param G: A congruence subgroup intermediate between Gamma0 and Gamma1
    :param start: an integer
    :param stop: an integer
    :return: the list of squarefree integers d between start and stop such that the
        twist of J(G) by d has positive analytic rank.
    """
    positive_rank = []
    for d in range(start, stop):
        if d == 0 or d == 1 or not is_squarefree(d):
            continue

        if not is_rank_of_twist_zero(G, d):
            positive_rank.append(d)

    return positive_rank


def write_results(G, start, stop, location):
    """
    Writes the results of positive_rank_twists_in_range(G, start, stop)
    to a file.

    :param G: A congruence subgroup intermediate between Gamma0 and Gamma1
    :param start: an integer
    :param stop: an integer
    :param location: where to write the results to.
    """
    result = positive_rank_twists_in_range(G, start, stop)
    with open(location, "w") as f:
        f.write(json.dumps(result, indent=2))


def main(start, stop, directory = "../positive_rank_lists/"):
    """
    Do all the analytic rank computations for the paper, for modular curves
    of genus one curves this is Section 2 of the paper.

    """



    for G, location in [
        (Gamma1(11), f"{directory}/11_list.json"),
        (Gamma1(13), f"{directory}/13_list.json"),
        (Gamma1(14), f"{directory}/14_list.json"),
        (Gamma1(15), f"{directory}/15_list.json"),
        (Gamma1(16), f"{directory}/16_list.json"),
        (Gamma1(18), f"{directory}/18_list.json"),
        (Gamma0(20), f"{directory}/2_10_list.json"),
        (Gamma0(24), f"{directory}/2_12_list.json"),
    ]:
        write_results(G, start, stop, location)


if __name__ == "__main__":
    """
    In order to reproduce the computations in this file simply run
    
        sage positive_rank_twists.py 
    
    from the command line in this directory.
    """
    main(-10000, 10000)
