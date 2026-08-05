"""bimodal_logic.cli - Thin CLI for standalone countermodel checking.

Provides the `bimodal-logic check` command that invokes Z3OracleProvider
and prints JSON results to stdout.

Usage:
    bimodal-logic check '<formula_json>'
    bimodal-logic check '<formula_json>' --timeout 10000
    bimodal-logic check '<formula_json>' --frame-class Base

Output format (to stdout):
    {"result": "valid", "countermodel": null}
    {"result": "invalid", "countermodel": {...}}
    {"result": "inconclusive", "countermodel": null}

Exit codes:
    0 - check completed and the solver decided (valid or invalid)
    1 - error (bad JSON, unsupported frame class, or no subcommand given)
    2 - inconclusive (the solver exhausted its timeout without deciding;
        this is NOT the same as "valid" -- it means no verdict was reached)
"""

from __future__ import annotations

import argparse
import json
import sys
from typing import Optional


def main(argv: Optional[list[str]] = None) -> None:
    """Main entry point for the bimodal-logic CLI.

    Args:
        argv: Command line arguments. Defaults to sys.argv[1:] when None.
              Pass an explicit list for testability.
    """
    parser = argparse.ArgumentParser(
        prog='bimodal-logic',
        description='Z3-based bimodal logic countermodel checker',
    )
    subparsers = parser.add_subparsers(dest='command')

    check_parser = subparsers.add_parser(
        'check',
        help='Check formula for countermodel',
    )
    check_parser.add_argument(
        'formula_json',
        type=str,
        help='Formula as a JSON string (dict with "tag" key)',
    )
    check_parser.add_argument(
        '--timeout',
        type=int,
        default=5000,
        metavar='MS',
        help='Solver timeout in milliseconds (default: 5000)',
    )
    check_parser.add_argument(
        '--frame-class',
        default='Base',
        metavar='CLASS',
        help='Frame class to check against (default: Base)',
    )

    args = parser.parse_args(argv)

    if args.command is None:
        parser.print_help(sys.stderr)
        sys.exit(1)

    if args.command == 'check':
        # Parse the formula JSON
        try:
            formula = json.loads(args.formula_json)
        except json.JSONDecodeError as e:
            print(f"Error: invalid JSON formula: {e}", file=sys.stderr)
            sys.exit(1)

        # Invoke Z3OracleProvider
        from .errors import OracleTimeoutError
        from .provider import Z3OracleProvider
        provider = Z3OracleProvider()

        frame_class = args.frame_class
        if frame_class not in provider.supported_frame_classes:
            print(
                f"Error: unsupported frame class '{frame_class}'. "
                f"Supported: {sorted(provider.supported_frame_classes)}",
                file=sys.stderr,
            )
            sys.exit(1)

        try:
            result = provider.find_countermodel(
                formula,
                frame_class=frame_class,
                timeout_ms=args.timeout,
            )
        except OracleTimeoutError:
            # The solver did not decide -- this must never be reported as
            # "valid", which would claim the formula was proven to have no
            # countermodel. Exit code 1 is already taken by input errors, so
            # a caller can distinguish "we don't know" from both "valid" and
            # "your input was bad".
            output = {"result": "inconclusive", "countermodel": None}
            print(json.dumps(output))
            sys.exit(2)

        if result is None:
            output = {"result": "valid", "countermodel": None}
        else:
            output = {"result": "invalid", "countermodel": result}

        print(json.dumps(output))
        sys.exit(0)


def run() -> None:
    """Entry point for the bimodal-logic console script."""
    main()
