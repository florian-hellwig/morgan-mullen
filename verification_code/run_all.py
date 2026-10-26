"""
run_all.py -- runs every computational check of the paper, on any system.
Same as run_all.sh, but needs no bash: on Windows (e.g. in the Anaconda Prompt) run
    python run_all.py
It uses the Python interpreter that runs this file, so the packages of the active environment are used.
Requirements: sympy, numpy, mpmath, galois   (pip install sympy numpy mpmath galois).  A few minutes.
"""
import os, subprocess, sys, time

STEPS = [
    ("1/8  Sections 2-3, Thm 4.2(a), Cor 8.8, 8.9(a) against the definition of CN (Lemma 2.3, Thm 2.5, 2.6, 3.2)", ["bruteforce_small_fields.py"]),
    ("2/8  exact maximal weights and the structure theorem (Thm 7.2, Prop 7.7)", ["struct_and_exactmax.py"]),
    ("3/8  weight bounds W(q) (Thm 7.8)", ["weights.py"]),
    ("4/8  local maxima and divisor sums for M (Prop 6.5)", ["bounds_for_M.py"]),
    ("5/8  analytic thresholds (Prop 8.3)", ["thresholds.py"]),
    ("6/8  finite ranges with exact M and S (Prop 8.4)", ["finite_ranges.py"]),
    ("7/8  the 70 PCN certificates (Prop 8.5)", ["pcn_certificates.py", "--verify"]),
    ("8/8  the examples of Sections 10 and 12 (not part of the proof)", ["examples.py"]),
]

if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    for title, cmd in STEPS:
        print("\n=================== " + title, flush=True)
        t0 = time.time()
        r = subprocess.run([sys.executable] + cmd, cwd=here)
        if r.returncode != 0:
            print(f"\nFAILED: {cmd[0]} exited with code {r.returncode}")
            sys.exit(r.returncode)
        print(f"[{time.time() - t0:.0f} s]", flush=True)
    print("\nALL CHECKS FINISHED")
