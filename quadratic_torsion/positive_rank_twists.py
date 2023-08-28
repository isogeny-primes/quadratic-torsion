from sage.all import ModularSymbols, kronecker_character, is_squarefree


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
        if d == 0 or not is_squarefree(d):
            continue

        if not is_rank_of_twist_zero(G, d):
            positive_rank.append(d)

    return positive_rank
