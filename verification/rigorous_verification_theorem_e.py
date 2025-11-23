#!/usr/bin/env python3
"""
Rigorous Computational Verification of Theorem E

Theorem E: For all odd n ≥ 7 with n ≡ 7 (mod 8),
there exists k ≤ ⌊log₂(n)⌋ such that C^k(n) ≡ 3 (mod 8).

This script exhaustively verifies the theorem for a large range.
"""

import math
from typing import Tuple, List

def collatz(n: int) -> int:
    """Collatz function: C(n) = n/2 if even, (3n+1)/2 if odd"""
    if n % 2 == 0:
        return n // 2
    else:
        return (3 * n + 1) // 2

def find_exit_to_3mod8(n: int) -> Tuple[int, List[int]]:
    """
    Find the number of steps until C^k(n) ≡ 3 (mod 8).

    Returns: (steps, trajectory)
    Raises: ValueError if trajectory escapes or cycles without exiting
    """
    if n % 8 != 7:
        raise ValueError(f"n = {n} is not ≡ 7 (mod 8)")

    trajectory = [n]
    current = n
    max_steps = 10000  # Safety limit

    for step in range(1, max_steps + 1):
        current = collatz(current)
        trajectory.append(current)

        if current % 8 == 3:
            return step, trajectory

        # Safety check: if value exceeds safety threshold
        if current > n * 1000:
            raise ValueError(f"Trajectory escaped: reached {current} from {n}")

    raise ValueError(f"Failed to exit after {max_steps} steps from n = {n}")

def verify_theorem_e(max_n: int = 1_000_000, verbose: bool = True) -> dict:
    """
    Verify Theorem E for all n ≡ 7 (mod 8) up to max_n.

    Returns: Dictionary with verification results
    """
    results = {
        'total_tested': 0,
        'max_steps': 0,
        'max_steps_n': 0,
        'max_ratio': 0.0,
        'max_ratio_n': 0,
        'failures': [],
        'all_passed': True
    }

    if verbose:
        print(f"Verifying Theorem E for n ≡ 7 (mod 8), n ∈ [7, {max_n}]")
        print("=" * 70)

    for n in range(7, max_n + 1, 8):
        if n % 8 != 7:
            continue

        results['total_tested'] += 1

        try:
            steps, trajectory = find_exit_to_3mod8(n)
            bound = math.floor(math.log2(n))

            # Check if steps ≤ bound
            if steps > bound:
                results['failures'].append({
                    'n': n,
                    'steps': steps,
                    'bound': bound,
                    'trajectory': trajectory
                })
                results['all_passed'] = False

                if verbose:
                    print(f"FAILURE: n = {n}, steps = {steps}, bound = {bound}")

            # Track statistics
            if steps > results['max_steps']:
                results['max_steps'] = steps
                results['max_steps_n'] = n

            ratio = steps / bound if bound > 0 else 0
            if ratio > results['max_ratio']:
                results['max_ratio'] = ratio
                results['max_ratio_n'] = n

        except Exception as e:
            results['failures'].append({
                'n': n,
                'error': str(e)
            })
            results['all_passed'] = False
            if verbose:
                print(f"ERROR at n = {n}: {e}")

        # Progress update
        if verbose and results['total_tested'] % 10000 == 0:
            print(f"Tested {results['total_tested']:,} values...")

    if verbose:
        print("\n" + "=" * 70)
        print("VERIFICATION RESULTS")
        print("=" * 70)
        print(f"Total tested: {results['total_tested']:,}")
        print(f"All passed: {results['all_passed']}")
        print(f"Failures: {len(results['failures'])}")
        print(f"\nMaximum steps: {results['max_steps']} (at n = {results['max_steps_n']:,})")
        print(f"Maximum ratio steps/log₂(n): {results['max_ratio']:.3f} (at n = {results['max_ratio_n']:,})")

        if results['failures']:
            print(f"\nFirst few failures:")
            for failure in results['failures'][:5]:
                print(f"  {failure}")

    return results

def verify_lemma_e1(max_n: int = 100000) -> bool:
    """
    Verify Lemma E.1: For n ≡ 7 (mod 16), C(n) ≡ 3 (mod 8).
    """
    print("\nVerifying Lemma E.1...")
    failures = 0

    for n in range(7, max_n + 1, 16):
        if n % 16 != 7:
            continue

        cn = collatz(n)
        if cn % 8 != 3:
            print(f"FAILURE: n = {n}, C(n) = {cn}, C(n) mod 8 = {cn % 8}")
            failures += 1

    if failures == 0:
        print(f"✓ Lemma E.1 verified for all n ∈ [7, {max_n}], n ≡ 7 (mod 16)")
        return True
    else:
        print(f"✗ Lemma E.1 FAILED: {failures} failures")
        return False

def verify_lemma_e2(max_n: int = 100000) -> bool:
    """
    Verify Lemma E.2: For n ≡ 7 (mod 8), C(n) ≡ 7 (mod 8) ⟺ n ≡ 15 (mod 16).
    """
    print("\nVerifying Lemma E.2...")
    failures = 0

    for n in range(7, max_n + 1, 8):
        if n % 8 != 7:
            continue

        cn = collatz(n)
        cn_mod8 = cn % 8
        n_mod16 = n % 16

        # Check ⟹ direction: if C(n) ≡ 7 (mod 8), then n ≡ 15 (mod 16)
        if cn_mod8 == 7 and n_mod16 != 15:
            print(f"FAILURE (⟹): n = {n}, n mod 16 = {n_mod16}, C(n) mod 8 = {cn_mod8}")
            failures += 1

        # Check ⟸ direction: if n ≡ 15 (mod 16), then C(n) ≡ 7 (mod 8)
        if n_mod16 == 15 and cn_mod8 != 7:
            print(f"FAILURE (⟸): n = {n}, n mod 16 = {n_mod16}, C(n) mod 8 = {cn_mod8}")
            failures += 1

    if failures == 0:
        print(f"✓ Lemma E.2 verified for all n ∈ [7, {max_n}], n ≡ 7 (mod 8)")
        return True
    else:
        print(f"✗ Lemma E.2 FAILED: {failures} failures")
        return False

def analyze_exit_times(max_n: int = 10000):
    """Analyze the distribution of exit times."""
    print("\n" + "=" * 70)
    print("EXIT TIME ANALYSIS")
    print("=" * 70)

    exit_times = {}

    for n in range(7, max_n + 1, 8):
        if n % 8 != 7:
            continue

        steps, _ = find_exit_to_3mod8(n)

        if steps not in exit_times:
            exit_times[steps] = []
        exit_times[steps].append(n)

    print(f"\nDistribution of exit times for n ≤ {max_n}:")
    print(f"{'Steps':<10} {'Count':<10} {'Example n values'}")
    print("-" * 70)

    for steps in sorted(exit_times.keys()):
        examples = exit_times[steps][:5]
        print(f"{steps:<10} {len(exit_times[steps]):<10} {examples}")

    max_steps = max(exit_times.keys())
    worst_cases = exit_times[max_steps]
    print(f"\nMaximum exit time: {max_steps} steps")
    print(f"Occurs at n = {worst_cases}")

def main():
    print("RIGOROUS VERIFICATION OF THEOREM E")
    print("=" * 70)

    # Verify lemmas first
    lemma_e1_ok = verify_lemma_e1(max_n=100000)
    lemma_e2_ok = verify_lemma_e2(max_n=100000)

    if not (lemma_e1_ok and lemma_e2_ok):
        print("\n⚠ Lemmas failed! Stopping verification.")
        return

    # Verify main theorem
    print("\n" + "=" * 70)
    results = verify_theorem_e(max_n=1_000_000, verbose=True)

    # Analyze exit times
    analyze_exit_times(max_n=10000)

    # Final verdict
    print("\n" + "=" * 70)
    print("FINAL VERDICT")
    print("=" * 70)
    if results['all_passed']:
        print("✓✓✓ THEOREM E VERIFIED ✓✓✓")
        print(f"All {results['total_tested']:,} test cases passed!")
        print(f"Verified for all n ≡ 7 (mod 8), n ∈ [7, 1,000,000]")
    else:
        print("✗✗✗ THEOREM E FAILED ✗✗✗")
        print(f"Found {len(results['failures'])} failures")

if __name__ == "__main__":
    main()
