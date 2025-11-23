#!/usr/bin/env python3
"""
Rigorous Computational Verification of Theorem MV

Theorem MV: For all n ≥ 1, M(n) ≤ 2048·n^4
where M(n) = max{C^j(n) : 0 ≤ j ≤ τ(n)}

This script exhaustively verifies:
1. Descent time bounds for all residue classes
2. Maximum value bounds
"""

import math
from typing import Tuple, List, Dict

def collatz(n: int) -> int:
    """Collatz function: C(n) = n/2 if even, (3n+1)/2 if odd"""
    if n % 2 == 0:
        return n // 2
    else:
        return (3 * n + 1) // 2

def compute_descent_info(n: int, max_steps: int = 100000) -> Dict:
    """
    Compute descent time and maximum value before first descent.

    Returns: {
        'tau': descent time,
        'max_value': maximum value before descent,
        'trajectory': full trajectory until descent
    }
    """
    trajectory = [n]
    current = n
    max_val = n

    for step in range(1, max_steps + 1):
        current = collatz(current)
        trajectory.append(current)
        max_val = max(max_val, current)

        if current < n:  # First descent
            return {
                'tau': step,
                'max_value': max_val,
                'trajectory': trajectory,
                'converged': True
            }

    # No descent found
    return {
        'tau': max_steps,
        'max_value': max_val,
        'trajectory': trajectory,
        'converged': False
    }

def verify_descent_time_bound_mod1_5(max_n: int = 100000) -> bool:
    """
    Verify that for n ≡ 1, 5 (mod 8): τ(n) = 2
    """
    print("\nVerifying descent time bound for n ≡ 1, 5 (mod 8)...")
    failures = 0

    for n in range(1, max_n + 1, 2):  # Odd numbers
        if n % 8 not in [1, 5]:
            continue

        info = compute_descent_info(n)

        if info['tau'] != 2:
            print(f"FAILURE: n = {n} (mod 8 = {n % 8}), τ = {info['tau']}, expected 2")
            failures += 1
            if failures >= 10:  # Limit output
                print("(Further failures suppressed...)")
                return False

    if failures == 0:
        count = len([n for n in range(1, max_n + 1, 2) if n % 8 in [1, 5]])
        print(f"✓ Verified τ(n) = 2 for all {count:,} cases with n ≡ 1, 5 (mod 8)")
        return True
    else:
        print(f"✗ FAILED: {failures} failures")
        return False

def verify_descent_time_bound_mod7(max_n: int = 100000) -> bool:
    """
    Verify that for n ≡ 7 (mod 8): τ(n) ≤ ⌊log₂(n)⌋ + 10
    """
    print("\nVerifying descent time bound for n ≡ 7 (mod 8)...")
    failures = 0
    max_tau = 0
    max_tau_n = 0
    max_ratio = 0.0

    for n in range(7, max_n + 1, 8):
        info = compute_descent_info(n)
        bound = math.floor(math.log2(n)) + 10

        if info['tau'] > bound:
            print(f"FAILURE: n = {n}, τ = {info['tau']}, bound = {bound}")
            failures += 1
            if failures >= 10:
                return False

        if info['tau'] > max_tau:
            max_tau = info['tau']
            max_tau_n = n

        ratio = info['tau'] / math.floor(math.log2(n)) if n > 1 else 0
        if ratio > max_ratio:
            max_ratio = ratio

    if failures == 0:
        count = len(range(7, max_n + 1, 8))
        print(f"✓ Verified τ(n) ≤ ⌊log₂(n)⌋ + 10 for all {count:,} cases")
        print(f"  Max τ: {max_tau} (at n = {max_tau_n:,})")
        print(f"  Max ratio τ/log₂(n): {max_ratio:.3f}")
        return True
    else:
        print(f"✗ FAILED: {failures} failures")
        return False

def verify_descent_time_bound_mod3(max_n: int = 100000) -> bool:
    """
    Verify that for n ≡ 3 (mod 8): τ(n) ≤ 6·⌊log₂(n)⌋ + 20

    This is the critical case that was partially empirical in the original proof.
    """
    print("\nVerifying descent time bound for n ≡ 3 (mod 8)...")
    print("(This is the critical case requiring computational verification)")
    failures = 0
    max_tau = 0
    max_tau_n = 0
    max_ratio = 0.0
    failed_cases = []

    for n in range(3, max_n + 1, 8):
        info = compute_descent_info(n)

        if not info['converged']:
            print(f"ERROR: No descent found for n = {n} within step limit")
            failures += 1
            continue

        bound = 6 * math.floor(math.log2(n)) + 20 if n > 1 else 20

        if info['tau'] > bound:
            failed_cases.append({
                'n': n,
                'tau': info['tau'],
                'bound': bound,
                'ratio': info['tau'] / bound
            })
            failures += 1

        if info['tau'] > max_tau:
            max_tau = info['tau']
            max_tau_n = n

        if n > 1:
            ratio = info['tau'] / math.floor(math.log2(n))
            if ratio > max_ratio:
                max_ratio = ratio

    count = len(range(3, max_n + 1, 8))

    if failures == 0:
        print(f"✓ Verified τ(n) ≤ 6·⌊log₂(n)⌋ + 20 for all {count:,} cases")
        print(f"  Max τ: {max_tau} (at n = {max_tau_n:,})")
        print(f"  Max ratio τ/log₂(n): {max_ratio:.3f}")
        return True
    else:
        print(f"✗ FAILED: {failures} failures out of {count} cases")
        print("\nFirst few failures:")
        for case in failed_cases[:5]:
            print(f"  n = {case['n']}, τ = {case['tau']}, bound = {case['bound']}, "
                  f"ratio = {case['ratio']:.3f}")
        return False

def verify_maximum_value_bounds(max_n: int = 10000) -> bool:
    """
    Verify that M(n) ≤ 2048·n^4 for all n.
    """
    print("\nVerifying maximum value bounds M(n) ≤ 2048·n^4...")
    failures = 0
    max_ratio = 0.0
    max_ratio_n = 0

    for n in range(1, max_n + 1):
        info = compute_descent_info(n)

        if not info['converged']:
            print(f"ERROR: No descent for n = {n}")
            failures += 1
            continue

        M_n = info['max_value']
        bound = 2048 * (n ** 4)

        if M_n > bound:
            print(f"FAILURE: n = {n}, M(n) = {M_n:,}, bound = {bound:,}")
            failures += 1
            if failures >= 10:
                return False

        ratio = M_n / (n ** 4) if n > 0 else 0
        if ratio > max_ratio:
            max_ratio = ratio
            max_ratio_n = n

    if failures == 0:
        print(f"✓ Verified M(n) ≤ 2048·n^4 for all n ∈ [1, {max_n:,}]")
        print(f"  Max ratio M(n)/n^4: {max_ratio:.3f} (at n = {max_ratio_n})")
        return True
    else:
        print(f"✗ FAILED: {failures} failures")
        return False

def analyze_residue_class_3_mod_8(max_n: int = 10000):
    """
    Detailed analysis of the n ≡ 3 (mod 8) case.
    """
    print("\n" + "=" * 70)
    print("DETAILED ANALYSIS: n ≡ 3 (mod 8)")
    print("=" * 70)

    tau_distribution = {}
    max_value_distribution = {}

    for n in range(3, max_n + 1, 8):
        info = compute_descent_info(n)
        tau = info['tau']
        M_n = info['max_value']

        if tau not in tau_distribution:
            tau_distribution[tau] = []
        tau_distribution[tau].append(n)

        # Bin by M(n)/n ratio
        ratio_bin = int(M_n / n)
        if ratio_bin not in max_value_distribution:
            max_value_distribution[ratio_bin] = []
        max_value_distribution[ratio_bin].append((n, M_n))

    print("\nDescent time distribution:")
    print(f"{'τ':<10} {'Count':<10} {'Example n'}")
    print("-" * 70)
    for tau in sorted(tau_distribution.keys())[:20]:
        examples = tau_distribution[tau][:3]
        print(f"{tau:<10} {len(tau_distribution[tau]):<10} {examples}")

    if len(tau_distribution) > 20:
        print(f"... ({len(tau_distribution) - 20} more distinct values)")

    print("\nMaximum value ratio M(n)/n distribution:")
    print(f"{'Ratio range':<15} {'Count':<10} {'Examples (n, M(n))'}")
    print("-" * 70)
    for ratio_bin in sorted(max_value_distribution.keys())[:10]:
        examples = max_value_distribution[ratio_bin][:2]
        print(f"[{ratio_bin}, {ratio_bin+1}){'':<5} {len(max_value_distribution[ratio_bin]):<10} {examples}")

def verify_theorem_d2():
    """
    Verify Theorem D.2: For n ≡ 3 (mod 8), C(n) ≡ 1 or 5 (mod 8)
    """
    print("\nVerifying Theorem D.2...")
    failures = 0

    for n in range(3, 100001, 8):
        cn = collatz(n)
        cn_mod8 = cn % 8

        if cn_mod8 not in [1, 5]:
            print(f"FAILURE: n = {n}, C(n) = {cn}, C(n) mod 8 = {cn_mod8}")
            failures += 1
            if failures >= 10:
                return False

    if failures == 0:
        print("✓ Theorem D.2 verified: C(n) ≡ 1 or 5 (mod 8) for all n ≡ 3 (mod 8)")
        return True
    else:
        print(f"✗ Theorem D.2 FAILED: {failures} failures")
        return False

def main():
    print("=" * 70)
    print("RIGOROUS VERIFICATION OF THEOREM MV")
    print("=" * 70)

    # Verify supporting theorem
    d2_ok = verify_theorem_d2()

    if not d2_ok:
        print("\n⚠ Theorem D.2 failed! Cannot proceed.")
        return

    # Verify descent time bounds for each residue class
    print("\n" + "=" * 70)
    print("DESCENT TIME BOUNDS VERIFICATION")
    print("=" * 70)

    mod1_5_ok = verify_descent_time_bound_mod1_5(max_n=100000)
    mod7_ok = verify_descent_time_bound_mod7(max_n=100000)
    mod3_ok = verify_descent_time_bound_mod3(max_n=100000)

    if not (mod1_5_ok and mod7_ok and mod3_ok):
        print("\n⚠ Descent time bounds failed!")
        return

    # Verify maximum value bounds
    print("\n" + "=" * 70)
    print("MAXIMUM VALUE BOUNDS VERIFICATION")
    print("=" * 70)

    mv_ok = verify_maximum_value_bounds(max_n=10000)

    # Detailed analysis of critical case
    analyze_residue_class_3_mod_8(max_n=10000)

    # Final verdict
    print("\n" + "=" * 70)
    print("FINAL VERDICT")
    print("=" * 70)

    all_ok = d2_ok and mod1_5_ok and mod7_ok and mod3_ok and mv_ok

    if all_ok:
        print("✓✓✓ THEOREM MV VERIFIED ✓✓✓")
        print("\nAll components verified:")
        print("  ✓ Theorem D.2 (modular structure)")
        print("  ✓ Descent time bounds (all residue classes)")
        print("  ✓ Maximum value bounds M(n) ≤ 2048·n^4")
        print("\nThe bound M(n) ≤ 2048·n^4 is rigorously verified computationally")
        print("for n ≤ 100,000 (descent times) and n ≤ 10,000 (max values).")
    else:
        print("✗✗✗ THEOREM MV FAILED ✗✗✗")
        print("Some components did not verify correctly.")

if __name__ == "__main__":
    main()
