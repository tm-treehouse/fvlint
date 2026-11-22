# SPDX-FileCopyrightText: 2026 The fvlint Authors
# SPDX-License-Identifier: ISC
"""Unit tests for fvlint's internals.  No Yosys, SymbiYosys or solver needed.

    python -m unittest discover -s tests/unit -t .

FVLINT_SRC overrides the source tree under test (the mutation runner uses it
to test mutated copies).
"""

import os
import sys

_SRC = os.environ.get("FVLINT_SRC") or os.path.join(os.path.dirname(__file__), "..", "..", "src")
sys.path.insert(0, os.path.abspath(_SRC))
