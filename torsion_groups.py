"""torsion_groups.py

    Return finite list of torsion groups attached to a quadratic number field.

    ====================================================================

    This file is part of quadratic-torsion.

    Copyright (C) 2023 Barinder S. Banwait and Maarten Derickx

    Quadratic Torsion is free software: you can redistribute it and/or
    modify it under the terms of the GNU General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

    The authors can be reached at: barinder.s.banwait@gmail.com and
    maarten@mderickx.nl.

    ====================================================================

"""

import argparse
import logging
from inspect import cleandoc


RATIONAL_TORSION_GROUPS = [
    *[(1, N) for N in range(1, 13) if N != 11],
    *[(2, 2 * N) for N in range(1, 5)],
]

QUADRATIC_TORSION_GROUPS = [
    *[(1, N) for N in range(1, 19) if N != 17],
    *[(2, 2 * N) for N in range(1, 7)],
    *[(3, 3 * N) for N in range(1, 3)],
    (4, 4),
]


def quadratic_torsion_groups(_):
    lower_bound = set(RATIONAL_TORSION_GROUPS)
    upper_bound = set(QUADRATIC_TORSION_GROUPS)
    return lower_bound, upper_bound


########################################################################
#                                                                      #
#                            CLI HANDLER                               #
#                                                                      #
########################################################################


def cli_handler(args):
    d = args.d

    loglevel = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        format="%(asctime)s %(levelname)s: %(message)s",
        datefmt="%H:%M:%S",
        level=loglevel,
    )
    logging.debug("Debugging level for log messages set.")

    lower_bound, upper_bound = quadratic_torsion_groups(d)
    unknown = sorted(upper_bound - lower_bound)
    known = sorted(lower_bound - set(RATIONAL_TORSION_GROUPS))
    logging.info(f"Superset = {sorted(upper_bound)}")

    logging.info(f"Certified new torsion groups = {known}")

    logging.info(f"Possible new torsion groups = {unknown}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "d",
        metavar="d",
        type=int,
        help=cleandoc(
            """
            The discriminant quadratic numberfield.
            If d is not a discriminant it is replaced by the discriminant of Q(\sqrt{d}).
            """
        ),
    )
    parser.add_argument("--verbose", action="store_true", help="get more info printed")
    args = parser.parse_args()
    cli_handler(args)
