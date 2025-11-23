#!/usr/bin/env python3
"""
Extended Computational Verification for n ≡ 3 (mod 8)

This script provides comprehensive computational verification for the
critical n ≡ 3 (mod 8) case, which lacks complete analytical proof.

Verification Goals:
1. Verify τ(n) < ∞ for all n ≡ 3 (mod 8) up to 10^7
2. Analyze distribution of descent times
3. Identify maximum descent times and values
4. Provide statistical evidence for universal descent
"""

import sys
from typing import Dict, List, Tuple
import math

def collatz(n: int) -> int:
    """Collatz function: C(n) = n/2 if even, (3n+1)/2 if odd"""
    if n % 2 == 0:
        return n // 2
    else:
        return (3 * n + 1) // 2

def compute_descent_info(n: int, max_steps: int = 1000000) -> Dict:
    """
    Compute descent time τ(n) and maximum value M(n) before first descent.

    Returns: {
        'tau': descent time (steps until C^k(n) < n),
        'max_value': maximum value in trajectory before descent,
        'descent_value': value at first descent,
        'converged': whether descent was found
    }
    """
    current = n
    max_val = n

    for step in range(1, max_steps + 1):
        current = collatz(current)
        max_val = max(max_val, current)

        if current < n:  # First descent
            return {
                'tau': step,
                'max_value': max_val,
                'descent_value': current,
                'converged': True
            }

    # No descent found within step limit
    return {
        'tau': max_steps,
        'max_value': max_val,
        'descent_value': current,
        'converged': False
    }

def verify_mod3_case(max_n: int = 10000000, report_interval: int = 100000) -> Dict:
    """
    Comprehensive verification for n ≡ 3 (mod 8).

    Args:
        max_n: Maximum n to test
        report_interval: How often to print progress

    Returns:
        Dictionary with verification results and statistics
    """
    print("=" * 80)
    print(f"EXTENDED VERIFICATION: n ≡ 3 (mod 8) up to {max_n:,}")
    print("=" * 80)
    print()

    # Statistics
    total_tested = 0
    failures = []

    # Descent time statistics
    tau_max = 0
    tau_max_n = 0
    tau_distribution = {}

    # Maximum value statistics
    max_value_peak = 0
    max_value_peak_n = 0
    max_ratio = 0.0
    max_ratio_n = 0

    # Interesting cases
    large_tau_cases = []  # Cases with τ > 50
    large_max_cases = []   # Cases with M(n)/n > 20

    # Progress
    next_report = report_interval

    print("Testing all n ≡ 3 (mod 8) from 3 to {:,}...".format(max_n))
    print()

    for n in range(3, max_n + 1, 8):
        total_tested += 1

        # Progress report
        if n >= next_report:
            print(f"Progress: n = {n:,} (tested {total_tested:,} values, max τ = {tau_max})")
            next_report += report_interval

        # Compute descent info
        info = compute_descent_info(n)

        # Check for failure
        if not info['converged']:
            failures.append(n)
            print(f"  ⚠ WARNING: No descent found for n = {n:,} within step limit!")
            if len(failures) >= 10:
                print("  Too many failures, stopping...")
                break

        # Update statistics
        tau = info['tau']
        max_val = info['max_value']

        # Track τ distribution
        if tau not in tau_distribution:
            tau_distribution[tau] = []
        tau_distribution[tau].append(n)

        # Track maximum τ
        if tau > tau_max:
            tau_max = tau
            tau_max_n = n

        # Track maximum values
        if max_val > max_value_peak:
            max_value_peak = max_val
            max_value_peak_n = n

        ratio = max_val / n
        if ratio > max_ratio:
            max_ratio = ratio
            max_ratio_n = n

        # Track interesting cases
        if tau > 50:
            large_tau_cases.append((n, tau, max_val))
            if len(large_tau_cases) <= 10:  # Report first 10
                print(f"  Large τ: n = {n:,}, τ = {tau}, M(n) = {max_val:,}")

        if ratio > 20:
            large_max_cases.append((n, max_val, ratio))
            if len(large_max_cases) <= 10:  # Report first 10
                print(f"  Large M(n)/n: n = {n:,}, M(n) = {max_val:,}, ratio = {ratio:.2f}")

    print()
    print("=" * 80)
    print("VERIFICATION RESULTS")
    print("=" * 80)
    print()

    # Overall result
    success = len(failures) == 0

    if success:
        print("✓✓✓ ALL TESTS PASSED ✓✓✓")
        print()
        print(f"Universal descent verified for all {total_tested:,} values of n ≡ 3 (mod 8)")
        print(f"in the range [3, {max_n:,}].")
    else:
        print("✗✗✗ FAILURES DETECTED ✗✗✗")
        print()
        print(f"Failed to find descent for {len(failures)} values:")
        print(f"  {failures}")
        return {
            'success': False,
            'failures': failures,
            'total_tested': total_tested
        }

    print()
    print("DESCENT TIME STATISTICS:")
    print("-" * 80)
    print(f"  Maximum τ: {tau_max} (at n = {tau_max_n:,})")
    print(f"  Number of distinct τ values: {len(tau_distribution)}")
    print(f"  τ distribution (top 20):")

    sorted_taus = sorted(tau_distribution.keys())[:20]
    for tau in sorted_taus:
        count = len(tau_distribution[tau])
        examples = tau_distribution[tau][:3]
        print(f"    τ = {tau:3d}: {count:6d} cases (e.g., n = {examples})")

    if len(tau_distribution) > 20:
        print(f"    ... ({len(tau_distribution) - 20} more distinct values)")

    print()
    print("MAXIMUM VALUE STATISTICS:")
    print("-" * 80)
    print(f"  Largest M(n): {max_value_peak:,} (at n = {max_value_peak_n:,})")
    print(f"  Largest ratio M(n)/n: {max_ratio:.2f} (at n = {max_ratio_n:,})")
    print(f"  Number of cases with τ > 50: {len(large_tau_cases)}")
    print(f"  Number of cases with M(n)/n > 20: {len(large_max_cases)}")

    if large_tau_cases:
        print()
        print("TOP CASES BY DESCENT TIME:")
        print("-" * 80)
        top_tau = sorted(large_tau_cases, key=lambda x: x[1], reverse=True)[:10]
        print(f"  {'n':>12}  {'τ':>6}  {'M(n)':>15}  {'M(n)/n':>8}")
        for n, tau, max_val in top_tau:
            ratio = max_val / n
            print(f"  {n:>12,}  {tau:>6}  {max_val:>15,}  {ratio:>8.2f}")

    if large_max_cases:
        print()
        print("TOP CASES BY MAXIMUM VALUE RATIO:")
        print("-" * 80)
        top_max = sorted(large_max_cases, key=lambda x: x[2], reverse=True)[:10]
        print(f"  {'n':>12}  {'M(n)':>15}  {'M(n)/n':>8}")
        for n, max_val, ratio in top_max:
            print(f"  {n:>12,}  {max_val:>15,}  {ratio:>8.2f}")

    print()
    print("=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print()
    print(f"✓ Universal descent (τ(n) < ∞) verified for ALL {total_tested:,} values")
    print(f"  of n ≡ 3 (mod 8) in the range [3, {max_n:,}].")
    print()
    print("This computational verification supports the hybrid proof approach,")
    print("where the well-ordering argument combines analytical methods with")
    print("computational base case verification.")
    print()

    return {
        'success': True,
        'total_tested': total_tested,
        'tau_max': tau_max,
        'tau_max_n': tau_max_n,
        'max_value_peak': max_value_peak,
        'max_value_peak_n': max_value_peak_n,
        'max_ratio': max_ratio,
        'max_ratio_n': max_ratio_n,
        'tau_distribution': tau_distribution,
        'large_tau_cases': large_tau_cases,
        'large_max_cases': large_max_cases,
        'failures': []
    }

def verify_theorem_d2(max_n: int = 10000000):
    """
    Verify Theorem D.2: For n ≡ 3 (mod 8), C(n) ≡ 1 or 5 (mod 8)
    """
    print()
    print("=" * 80)
    print("VERIFYING THEOREM D.2")
    print("=" * 80)
    print()
    print(f"Testing: For all n ≡ 3 (mod 8), C(n) ≡ 1 or 5 (mod 8)")
    print(f"Range: [3, {max_n:,}]")
    print()

    failures = 0
    tested = 0

    for n in range(3, max_n + 1, 8):
        tested += 1
        cn = collatz(n)
        cn_mod8 = cn % 8

        if cn_mod8 not in [1, 5]:
            print(f"  ✗ FAILURE: n = {n:,}, C(n) = {cn:,}, C(n) mod 8 = {cn_mod8}")
            failures += 1
            if failures >= 10:
                print("  Too many failures, stopping...")
                break

    if failures == 0:
        print(f"✓ Theorem D.2 verified for all {tested:,} cases")
        print()
        return True
    else:
        print(f"✗ Theorem D.2 FAILED: {failures} failures found")
        print()
        return False

def main():
    """Main verification routine"""
    print()
    print("╔" + "═" * 78 + "╗")
    print("║" + " " * 78 + "║")
    print("║" + " EXTENDED COMPUTATIONAL VERIFICATION: n ≡ 3 (mod 8) ".center(78) + "║")
    print("║" + " " * 78 + "║")
    print("╚" + "═" * 78 + "╝")
    print()

    # Verify Theorem D.2 first
    d2_ok = verify_theorem_d2(max_n=10000000)

    if not d2_ok:
        print("⚠ Theorem D.2 verification failed. Cannot proceed.")
        return False

    # Extended verification of universal descent
    print()

    # Choose verification range based on available resources
    if len(sys.argv) > 1:
        max_n = int(sys.argv[1])
    else:
        max_n = 10000000  # 10 million

    results = verify_mod3_case(max_n=max_n, report_interval=max_n // 10)

    return results['success']

if __name__ == "__main__":
    try:
        success = main()
        sys.exit(0 if success else 1)
    except KeyboardInterrupt:
        print()
        print()
        print("Verification interrupted by user.")
        sys.exit(1)
    except Exception as e:
        print()
        print(f"Error during verification: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
