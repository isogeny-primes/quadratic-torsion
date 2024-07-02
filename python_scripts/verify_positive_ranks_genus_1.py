"""verify_positive_ranks_genus_1.py

    This script verifies the entries in the positive rank lists for the 
    modular curves of genus 1.

    To use it, simply run
    
        sage verify_positive_ranks_genus_1.py

    If you want to see debug information, run

        sage verify_positive_ranks_genus_1.py --verbose

"""

import json
import logging
import argparse
from sage.all import Gamma1, Gamma0

def verify_rank_with_other_methods(E, d_vals):
    rank_failures = []
    sage_failures = []
    for d in d_vals:
        Ed = E.quadratic_twist(d)
        try:
            logging.debug(f"Computing rank of {Ed} with d = {d}")
            rk = Ed.rank(only_use_mwrank=False, proof=True)
        except RuntimeError:
            sage_failures.append(d)
            continue

        if rk == 0:
            rank_failures.append(d)

    return rank_failures, sage_failures


def main(directory="../positive_rank_lists/"):
    
    success = True
    for G, location in [
        (Gamma1(11), f"{directory}/11_list.json"),
        (Gamma1(14), f"{directory}/14_list.json"),
        (Gamma1(15), f"{directory}/15_list.json"),
        (Gamma0(20), f"{directory}/2_10_list.json"),
        (Gamma0(24), f"{directory}/2_12_list.json"),
    ]:

        E = G.modular_abelian_variety().elliptic_curve()
        with open(location, "r") as f:
            d_vals = json.loads(f.read())
        logging.info(f"Verifying ranks for {G}")
        logging.debug(f"Twisting parameters: {d_vals}")
        rank_failures, sage_failures = verify_rank_with_other_methods(E, d_vals)
        if rank_failures:
            logging.info(f"Rank failures for {G}: {rank_failures}")
            success = False
        if sage_failures:
            logging.info(f"Sage failures for {G}: {sage_failures}")
            success = False
    if success:
        logging.info("Ranks have been successfully verified.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--verbose', action='store_true')
    args = parser.parse_args()

    if args.verbose:
        logging.basicConfig(level=logging.DEBUG)
    else:
        logging.basicConfig(level=logging.INFO)

    main()