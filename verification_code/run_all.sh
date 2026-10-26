#!/usr/bin/env bash
# Runs every computational check of the paper.  A few minutes on one core.
# Requirements: python3 with sympy, numpy, mpmath, galois   (pip install sympy numpy mpmath galois)
# Another interpreter can be chosen with  PYTHON=python bash run_all.sh  (on Windows use run_all.py instead).
set -e
cd "$(dirname "$0")"
PY="${PYTHON:-python3}"
run () { echo; echo "=================== $1"; shift; local t0=$SECONDS; "$PY" "$@"; echo "[$((SECONDS - t0)) s]"; }
run "1/8  Sections 2-3, Thm 4.2(a), Cor 8.8, 8.9(a) against the definition of CN (Lemma 2.3, Thm 2.5, 2.6, 3.2)"   bruteforce_small_fields.py
run "2/8  exact maximal weights and the structure theorem (Thm 7.2, Prop 7.7)"    struct_and_exactmax.py
run "3/8  weight bounds W(q) (Thm 7.8)"                                         weights.py
run "4/8  local maxima and divisor sums for M (Prop 6.5)"                       bounds_for_M.py
run "5/8  analytic thresholds (Prop 8.3)"                                       thresholds.py
run "6/8  finite ranges with exact M and S (Prop 8.4)"                          finite_ranges.py
run "7/8  the 70 PCN certificates (Prop 8.5)"                                   pcn_certificates.py --verify
run "8/8  the examples of Sections 10 and 12 (not part of the proof)"           examples.py
echo; echo "ALL CHECKS FINISHED"
