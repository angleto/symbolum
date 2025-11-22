#!/usr/bin/env python3
"""
Worst Case Analysis: n ≡ 7 (mod 8) and Odd-to-Odd Chains

This script deeply analyzes the remaining cases not covered by Theorem A,
focusing on finding patterns and bounds for n ≡ 3 (mod 8) and n ≡ 7 (mod 8).

Goal: Extend deterministic proof beyond 50% coverage.
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict
from collections import defaultdict

def collatz(n: int) -> int:
    """Apply one step of the Collatz function."""
    if n % 2 == 0:
        return n // 2
    else:
        return (3 * n + 1) // 2

def compute_trajectory_detailed(n: int, max_steps: int = 10000) -> Dict:
    """
    Compute detailed trajectory information.

    Returns:
        dict with keys:
        - 'trajectory': list of values
        - 'parities': list of parities (0=even, 1=odd)
        - 'odd_chain_lengths': list of consecutive odd values lengths
        - 'descent_step': first k where C^k(n) < n
        - 'max_value': maximum value reached
        - 'stopping_time': steps to reach 1
    """
    trajectory = [n]
    parities = [n % 2]
    current = n
    descent_step = None
    max_value = n

    for k in range(1, max_steps):
        current = collatz(current)
        trajectory.append(current)
        parities.append(current % 2)

        if current > max_value:
            max_value = current

        if descent_step is None and current < n:
            descent_step = k

        if current == 1:
            break

    # Compute odd chain lengths
    odd_chain_lengths = []
    current_chain = 0
    for p in parities:
        if p == 1:  # odd
            current_chain += 1
        else:  # even
            if current_chain > 0:
                odd_chain_lengths.append(current_chain)
                current_chain = 0
    if current_chain > 0:
        odd_chain_lengths.append(current_chain)

    return {
        'trajectory': trajectory,
        'parities': parities,
        'odd_chain_lengths': odd_chain_lengths,
        'descent_step': descent_step,
        'max_value': max_value,
        'stopping_time': len(trajectory) - 1
    }

def analyze_mod8_class(mod8_val: int, n_max: int = 10000) -> List[Dict]:
    """Analyze all odd numbers n ≡ mod8_val (mod 8) up to n_max."""
    results = []

    for n in range(mod8_val, n_max + 1, 8):
        if n % 2 == 1:  # ensure odd
            info = compute_trajectory_detailed(n)
            info['n'] = n
            results.append(info)

    return results

def find_odd_chain_patterns(results: List[Dict]):
    """
    Analyze patterns in odd-to-odd chains.

    Key question: What's the maximum length of consecutive odd values?
    """
    max_chain_by_n = {}
    all_chains = []

    for r in results:
        n = r['n']
        chains = r['odd_chain_lengths']
        if chains:
            max_chain = max(chains)
            max_chain_by_n[n] = max_chain
            all_chains.extend(chains)

    return {
        'max_chain_by_n': max_chain_by_n,
        'all_chains': all_chains,
        'overall_max': max(all_chains) if all_chains else 0
    }

def analyze_growth_factor(results: List[Dict]):
    """
    Analyze the maximum growth factor before descent.

    Key metric: max_value / n
    """
    growth_factors = []

    for r in results:
        n = r['n']
        max_val = r['max_value']
        factor = max_val / n
        growth_factors.append((n, factor, max_val))

    return growth_factors

def prove_4step_bound_mod3(n_max: int = 10000):
    """
    Attempt: Can we prove 4-step bound for n ≡ 3 (mod 8)?

    For n ≡ 3 (mod 8):
    - n is odd, n ≡ 3 (mod 4)
    - C(n) = (3n+1)/2 is odd
    - Need to track C²(n), C³(n), C⁴(n)
    """
    results_by_steps = {2: [], 3: [], 4: [], 5: [], 6: []}
    failures = []

    for n in range(3, n_max + 1, 8):  # n ≡ 3 (mod 8)
        trajectory = [n]
        current = n

        for k in range(1, 7):
            current = collatz(current)
            trajectory.append(current)

            if current < n:
                if k in results_by_steps:
                    results_by_steps[k].append(n)
                break
        else:
            # Didn't descend in 6 steps
            failures.append((n, trajectory))

    return results_by_steps, failures

def theoretical_analysis_mod7():
    """
    Theoretical analysis of n ≡ 7 (mod 8).

    For n ≡ 7 (mod 8):
    C(n) = (3n+1)/2

    Since n = 8k+7:
    3n+1 = 3(8k+7)+1 = 24k+22 = 2(12k+11)
    So C(n) = 12k+11

    Now 12k+11 mod 8:
    If k even (k=2j): 12k+11 = 24j+11 ≡ 3 (mod 8) [odd]
    If k odd (k=2j+1): 12k+11 = 24j+23 ≡ 7 (mod 8) [odd]

    So C(n) is always odd for n ≡ 7 (mod 8)!
    This explains why these are worst cases.
    """
    print("=" * 80)
    print("THEORETICAL ANALYSIS: n ≡ 7 (mod 8)")
    print("=" * 80)

    print("\nFor n ≡ 7 (mod 8), we have n = 8k+7")
    print("Then C(n) = (3n+1)/2 = (3(8k+7)+1)/2 = (24k+22)/2 = 12k+11")
    print()
    print("Analyzing 12k+11 (mod 8):")
    print("  If k even (k=2j): 12k+11 = 24j+11 ≡ 3 (mod 8) → C(n) ≡ 3 (mod 8) [odd]")
    print("  If k odd (k=2j+1): 12k+11 = 24j+23 ≡ 7 (mod 8) → C(n) ≡ 7 (mod 8) [odd]")
    print()
    print("CONCLUSION: C(n) is ALWAYS odd for n ≡ 7 (mod 8)")
    print("This creates odd-to-odd chains, explaining worst-case behavior!")
    print()

    # Verify with examples
    print("Verification:")
    for k in range(5):
        n = 8*k + 7
        if n > 0:
            cn = collatz(n)
            mod8 = cn % 8
            print(f"  n={n} (≡7 mod 8): C(n)={cn} (≡{mod8} mod 8) {'[odd]' if cn%2==1 else '[even]'}")

def analyze_descent_bound_conjecture(results: List[Dict]):
    """
    Conjecture: For all odd n, descent_time ≤ c * log₂(n) for some constant c.

    Test this empirically.
    """
    data = []

    for r in results:
        n = r['n']
        k = r['descent_step']
        if k is not None and n > 1:
            ratio = k / np.log2(n)
            data.append((n, k, ratio))

    if data:
        ratios = [x[2] for x in data]
        max_ratio = max(ratios)
        avg_ratio = np.mean(ratios)

        return {
            'data': data,
            'max_ratio': max_ratio,
            'avg_ratio': avg_ratio,
            'max_example': max(data, key=lambda x: x[2])
        }
    return None

def main():
    """Main analysis routine."""

    print("=" * 80)
    print("WORST CASE ANALYSIS: n ≡ 3, 7 (mod 8)")
    print("Goal: Find bounds for remaining 50% of odd numbers")
    print("=" * 80)

    # Theoretical analysis first
    theoretical_analysis_mod7()

    # Analyze n ≡ 3 (mod 8)
    print("\n" + "=" * 80)
    print("ANALYSIS: n ≡ 3 (mod 8)")
    print("=" * 80)

    results_3 = analyze_mod8_class(3, n_max=10000)

    print(f"\nAnalyzed {len(results_3)} numbers n ≡ 3 (mod 8)")

    # Odd chain analysis
    chains_3 = find_odd_chain_patterns(results_3)
    print(f"\nOdd chain analysis:")
    print(f"  Maximum consecutive odd values: {chains_3['overall_max']}")
    print(f"  Numbers with max chain:")
    for n, max_chain in sorted(chains_3['max_chain_by_n'].items(), key=lambda x: x[1], reverse=True)[:10]:
        print(f"    n={n}: {max_chain} consecutive odd values")

    # Growth factor analysis
    growth_3 = analyze_growth_factor(results_3)
    growth_3_sorted = sorted(growth_3, key=lambda x: x[1], reverse=True)
    print(f"\nGrowth factor analysis:")
    print(f"  Maximum growth (max_value/n):")
    for n, factor, max_val in growth_3_sorted[:10]:
        print(f"    n={n}: factor={factor:.2f}, max_value={max_val}")

    # Descent time analysis
    descent_3 = analyze_descent_bound_conjecture(results_3)
    if descent_3:
        print(f"\nDescent time vs log₂(n):")
        print(f"  Maximum k/log₂(n): {descent_3['max_ratio']:.2f}")
        print(f"  Average k/log₂(n): {descent_3['avg_ratio']:.2f}")
        print(f"  Worst example: n={descent_3['max_example'][0]}, k={descent_3['max_example'][1]}, ratio={descent_3['max_example'][2]:.2f}")

    # 4-step bound test
    print("\n4-Step Bound Test for n ≡ 3 (mod 8):")
    steps_results, failures = prove_4step_bound_mod3(n_max=10000)
    for k in sorted(steps_results.keys()):
        count = len(steps_results[k])
        print(f"  Descend in {k} steps: {count} numbers")
    if failures:
        print(f"  Failed to descend in ≤6 steps: {len(failures)} numbers")
        print(f"  Examples: {[f[0] for f in failures[:5]]}")

    # Analyze n ≡ 7 (mod 8)
    print("\n" + "=" * 80)
    print("ANALYSIS: n ≡ 7 (mod 8) [WORST CASE]")
    print("=" * 80)

    results_7 = analyze_mod8_class(7, n_max=10000)

    print(f"\nAnalyzed {len(results_7)} numbers n ≡ 7 (mod 8)")

    # Odd chain analysis
    chains_7 = find_odd_chain_patterns(results_7)
    print(f"\nOdd chain analysis:")
    print(f"  Maximum consecutive odd values: {chains_7['overall_max']}")
    print(f"  Numbers with max chain:")
    for n, max_chain in sorted(chains_7['max_chain_by_n'].items(), key=lambda x: x[1], reverse=True)[:10]:
        print(f"    n={n}: {max_chain} consecutive odd values")

    # Growth factor analysis
    growth_7 = analyze_growth_factor(results_7)
    growth_7_sorted = sorted(growth_7, key=lambda x: x[1], reverse=True)
    print(f"\nGrowth factor analysis:")
    print(f"  Maximum growth (max_value/n):")
    for n, factor, max_val in growth_7_sorted[:10]:
        print(f"    n={n}: factor={factor:.2f}, max_value={max_val}")

    # Descent time analysis
    descent_7 = analyze_descent_bound_conjecture(results_7)
    if descent_7:
        print(f"\nDescent time vs log₂(n):")
        print(f"  Maximum k/log₂(n): {descent_7['max_ratio']:.2f}")
        print(f"  Average k/log₂(n): {descent_7['avg_ratio']:.2f}")
        print(f"  Worst example: n={descent_7['max_example'][0]}, k={descent_7['max_example'][1]}, ratio={descent_7['max_example'][2]:.2f}")

    # Deep dive into specific worst cases
    print("\n" + "=" * 80)
    print("DEEP DIVE: Specific Worst Cases")
    print("=" * 80)

    worst_cases = [27, 703, 1407, 7279]
    for n in worst_cases:
        info = compute_trajectory_detailed(n)
        print(f"\nn = {n} (≡{n%8} mod 8):")
        print(f"  Descent step: {info['descent_step']}")
        print(f"  Max value: {info['max_value']} (growth factor: {info['max_value']/n:.2f})")
        print(f"  Stopping time: {info['stopping_time']}")
        print(f"  Odd chain lengths: {info['odd_chain_lengths'][:10]}{'...' if len(info['odd_chain_lengths']) > 10 else ''}")
        print(f"  Max consecutive odd: {max(info['odd_chain_lengths']) if info['odd_chain_lengths'] else 0}")

    # Conjecture formulation
    print("\n" + "=" * 80)
    print("CONJECTURES AND BOUNDS")
    print("=" * 80)

    all_results = results_3 + results_7
    all_descent = [r['descent_step'] for r in all_results if r['descent_step'] is not None]
    all_chains = []
    for r in all_results:
        all_chains.extend(r['odd_chain_lengths'])

    max_descent = max(all_descent)
    max_chain = max(all_chains) if all_chains else 0

    print(f"\nEmpirical bounds (n ≤ 10000):")
    print(f"  Maximum descent time: {max_descent} steps")
    print(f"  Maximum consecutive odd values: {max_chain}")
    print(f"  Maximum growth factor: {max(growth_3_sorted + growth_7_sorted, key=lambda x: x[1])[1]:.2f}")

    print(f"\nConjecture 1 (Bounded Odd Chains):")
    print(f"  For all odd n, the maximum consecutive odd values is ≤ c·log₂(n)")
    print(f"  Evidence: max_chain/log₂(n) ≤ {max_chain / np.log2(max(r['n'] for r in all_results if max(r['odd_chain_lengths'], default=0) == max_chain)):.2f}")

    print(f"\nConjecture 2 (Bounded Descent Time):")
    print(f"  For all odd n, descent time ≤ c·log₂(n) for c ≈ 10-15")
    print(f"  Evidence: max observed ratio = {max(descent_3['max_ratio'], descent_7['max_ratio']):.2f}")

    # Visualization
    plot_worst_case_analysis(results_3, results_7)

    print("\n" + "=" * 80)
    print("ANALYSIS COMPLETE")
    print("=" * 80)

def plot_worst_case_analysis(results_3, results_7):
    """Create visualization of worst case analysis."""

    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    fig.suptitle('Worst Case Analysis: n ≡ 3, 7 (mod 8)', fontsize=16, fontweight='bold')

    # Plot 1: Descent time comparison
    ax = axes[0, 0]
    ns_3 = [r['n'] for r in results_3 if r['descent_step'] is not None]
    ks_3 = [r['descent_step'] for r in results_3 if r['descent_step'] is not None]
    ns_7 = [r['n'] for r in results_7 if r['descent_step'] is not None]
    ks_7 = [r['descent_step'] for r in results_7 if r['descent_step'] is not None]

    ax.scatter(ns_3, ks_3, alpha=0.5, s=10, label='n ≡ 3 (mod 8)', color='orange')
    ax.scatter(ns_7, ks_7, alpha=0.5, s=10, label='n ≡ 7 (mod 8)', color='red')
    ax.set_xlabel('n')
    ax.set_ylabel('Descent time')
    ax.set_title('Descent Time by Residue Class')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 2: Max odd chain length
    ax = axes[0, 1]
    max_chains_3 = [max(r['odd_chain_lengths'], default=0) for r in results_3]
    max_chains_7 = [max(r['odd_chain_lengths'], default=0) for r in results_7]

    ax.hist(max_chains_3, bins=range(1, max(max_chains_3)+2), alpha=0.6,
            label='n ≡ 3 (mod 8)', color='orange')
    ax.hist(max_chains_7, bins=range(1, max(max_chains_7)+2), alpha=0.6,
            label='n ≡ 7 (mod 8)', color='red')
    ax.set_xlabel('Max consecutive odd values')
    ax.set_ylabel('Frequency')
    ax.set_title('Distribution of Max Odd Chain Length')
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')

    # Plot 3: Growth factor
    ax = axes[0, 2]
    growth_3 = [r['max_value'] / r['n'] for r in results_3]
    growth_7 = [r['max_value'] / r['n'] for r in results_7]

    ax.hist(growth_3, bins=50, alpha=0.6, label='n ≡ 3 (mod 8)', color='orange')
    ax.hist(growth_7, bins=50, alpha=0.6, label='n ≡ 7 (mod 8)', color='red')
    ax.set_xlabel('Growth factor (max_value / n)')
    ax.set_ylabel('Frequency')
    ax.set_title('Distribution of Growth Factors')
    ax.legend()
    ax.grid(True, alpha=0.3, axis='y')

    # Plot 4: Descent time vs log(n)
    ax = axes[1, 0]
    if ns_3:
        ratios_3 = [k / np.log2(n) for n, k in zip(ns_3, ks_3) if n > 1]
        ax.scatter(ns_3, ratios_3, alpha=0.5, s=10, label='n ≡ 3 (mod 8)', color='orange')
    if ns_7:
        ratios_7 = [k / np.log2(n) for n, k in zip(ns_7, ks_7) if n > 1]
        ax.scatter(ns_7, ratios_7, alpha=0.5, s=10, label='n ≡ 7 (mod 8)', color='red')

    ax.set_xlabel('n')
    ax.set_ylabel('k / log₂(n)')
    ax.set_title('Descent Time Ratio vs n')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 5: Odd chain length vs n
    ax = axes[1, 1]
    ns_chains_3 = [r['n'] for r in results_3]
    ns_chains_7 = [r['n'] for r in results_7]

    ax.scatter(ns_chains_3, max_chains_3, alpha=0.5, s=10,
              label='n ≡ 3 (mod 8)', color='orange')
    ax.scatter(ns_chains_7, max_chains_7, alpha=0.5, s=10,
              label='n ≡ 7 (mod 8)', color='red')
    ax.set_xlabel('n')
    ax.set_ylabel('Max consecutive odd values')
    ax.set_title('Odd Chain Length vs n')
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 6: Growth vs descent time
    ax = axes[1, 2]
    growth_vs_descent_3 = [(r['max_value']/r['n'], r['descent_step'])
                           for r in results_3 if r['descent_step'] is not None]
    growth_vs_descent_7 = [(r['max_value']/r['n'], r['descent_step'])
                           for r in results_7 if r['descent_step'] is not None]

    if growth_vs_descent_3:
        gf_3, dt_3 = zip(*growth_vs_descent_3)
        ax.scatter(gf_3, dt_3, alpha=0.5, s=10, label='n ≡ 3 (mod 8)', color='orange')
    if growth_vs_descent_7:
        gf_7, dt_7 = zip(*growth_vs_descent_7)
        ax.scatter(gf_7, dt_7, alpha=0.5, s=10, label='n ≡ 7 (mod 8)', color='red')

    ax.set_xlabel('Growth factor')
    ax.set_ylabel('Descent time')
    ax.set_title('Growth Factor vs Descent Time')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('worst_case_analysis.png', dpi=300, bbox_inches='tight')
    print(f"\n✓ Plot saved as 'worst_case_analysis.png'")

if __name__ == "__main__":
    main()
