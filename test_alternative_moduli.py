#!/usr/bin/env python3
"""
Test alternative modular arithmetic for n ≡ 3 (mod 8) case

Question: Does mod 3, 5, or 7 reveal useful structure that mod 8 doesn't?

For each modulus, we'll analyze:
1. What residue classes does C(n) produce?
2. Is there persistent structure (like n ≡ 7 mod 8 persists)?
3. Do any classes guarantee descent?
4. Can we build a constraint-tightening argument?
"""

from collections import defaultdict, Counter

def collatz(n):
    """Standard Collatz function: n/2 if even, (3n+1)/2 if odd"""
    if n % 2 == 0:
        return n // 2
    else:
        return (3 * n + 1) // 2

def compute_trajectory(n, max_steps=10000):
    """Compute full trajectory until reaching 1 or max_steps"""
    trajectory = [n]
    current = n
    for _ in range(max_steps):
        if current == 1:
            break
        current = collatz(current)
        trajectory.append(current)
    return trajectory

# Test Mod 3
def analyze_mod_3():
    """
    Analyze Collatz behavior mod 3

    Key insight: 3n+1 ≡ 1 (mod 3) always!
    So C(n) = (3n+1)/2^a ≡ 1/2^a (mod 3)

    Need to understand powers of 2 mod 3:
    2^1 ≡ 2 (mod 3)
    2^2 ≡ 1 (mod 3)
    2^3 ≡ 2 (mod 3)
    ...
    Pattern: 2^k ≡ 2 if k odd, 1 if k even
    """
    print("="*80)
    print("MOD 3 ANALYSIS")
    print("="*80)
    print()

    # Theoretical analysis
    print("THEORETICAL ANALYSIS:")
    print()
    print("For odd n, 3n+1 ≡ 1 (mod 3) always")
    print("So C(n) = (3n+1)/2^a where a = number of trailing zeros")
    print()
    print("Powers of 2 mod 3:")
    for k in range(1, 11):
        print(f"  2^{k} ≡ {pow(2, k, 3)} (mod 3)")
    print()
    print("Pattern: 2^k ≡ 2 (mod 3) if k odd, 1 (mod 3) if k even")
    print()

    # Map: (n mod 3) -> (C(n) mod 3)
    print("Transition table for C(n) mod 3:")
    print()

    transitions = defaultdict(list)

    # Test many values
    for n in range(1, 1000, 2):  # odd only
        n_mod3 = n % 3
        cn = collatz(n)
        cn_mod3 = cn % 3
        transitions[n_mod3].append(cn_mod3)

    for n_mod3 in [0, 1, 2]:
        counter = Counter(transitions[n_mod3])
        print(f"  n ≡ {n_mod3} (mod 3):")
        for cn_mod3 in [0, 1, 2]:
            count = counter.get(cn_mod3, 0)
            pct = 100 * count / len(transitions[n_mod3]) if transitions[n_mod3] else 0
            print(f"    → C(n) ≡ {cn_mod3} (mod 3): {count} times ({pct:.1f}%)")
    print()

    # Test on n ≡ 3 (mod 8)
    print("For n ≡ 3 (mod 8), track trajectory mod 3:")
    print()

    # Test case: n = 27
    n = 27
    traj = compute_trajectory(n)
    traj_mod3 = [v % 3 for v in traj[:20]]  # first 20 steps

    print(f"n = {n} trajectory (first 20 steps):")
    print(f"  Values: {traj[:20]}")
    print(f"  Mod 3:  {traj_mod3}")
    print()

    # Distribution
    full_traj_mod3 = [v % 3 for v in traj]
    counter = Counter(full_traj_mod3)
    print(f"Full trajectory distribution mod 3 (n={n}):")
    for mod3 in [0, 1, 2]:
        count = counter.get(mod3, 0)
        pct = 100 * count / len(full_traj_mod3)
        print(f"  {mod3} (mod 3): {count}/{len(full_traj_mod3)} ({pct:.1f}%)")
    print()

    # Check if there's persistence
    print("Persistence check: Does trajectory stay in one mod 3 class?")
    unique_mod3 = set(full_traj_mod3)
    print(f"  Unique mod 3 classes visited: {sorted(unique_mod3)}")
    print(f"  Persistent? {'YES' if len(unique_mod3) == 1 else 'NO'}")
    print()

    return None

# Test Mod 5
def analyze_mod_5():
    """Analyze Collatz behavior mod 5"""
    print("="*80)
    print("MOD 5 ANALYSIS")
    print("="*80)
    print()

    # Transition table
    print("Transition table for C(n) mod 5 (for odd n):")
    print()

    transitions = defaultdict(list)

    # Test many values
    for n in range(1, 1000, 2):  # odd only
        n_mod5 = n % 5
        cn = collatz(n)
        cn_mod5 = cn % 5
        transitions[n_mod5].append(cn_mod5)

    for n_mod5 in [0, 1, 2, 3, 4]:
        counter = Counter(transitions[n_mod5])
        print(f"  n ≡ {n_mod5} (mod 5):")
        for cn_mod5 in [0, 1, 2, 3, 4]:
            count = counter.get(cn_mod5, 0)
            pct = 100 * count / len(transitions[n_mod5]) if transitions[n_mod5] else 0
            if count > 0:
                print(f"    → C(n) ≡ {cn_mod5} (mod 5): {count} times ({pct:.1f}%)")
    print()

    # Test on n ≡ 3 (mod 8)
    print("For n ≡ 3 (mod 8), track trajectory mod 5:")
    print()

    # Multiple test cases
    test_cases = [27, 91, 155, 219, 283]

    for n in test_cases:
        traj = compute_trajectory(n)
        traj_mod5 = [v % 5 for v in traj]

        counter = Counter(traj_mod5)
        unique_mod5 = set(traj_mod5)

        print(f"n = {n}:")
        print(f"  Mod 5 classes visited: {sorted(unique_mod5)}")
        print(f"  Persistent? {'YES' if len(unique_mod5) == 1 else 'NO'}")
    print()

    return None

# Test Mod 7
def analyze_mod_7():
    """Analyze Collatz behavior mod 7"""
    print("="*80)
    print("MOD 7 ANALYSIS")
    print("="*80)
    print()

    # Transition table
    print("Transition table for C(n) mod 7 (for odd n):")
    print()

    transitions = defaultdict(list)

    # Test many values
    for n in range(1, 1000, 2):  # odd only
        n_mod7 = n % 7
        cn = collatz(n)
        cn_mod7 = cn % 7
        transitions[n_mod7].append(cn_mod7)

    for n_mod7 in [0, 1, 2, 3, 4, 5, 6]:
        counter = Counter(transitions[n_mod7])
        print(f"  n ≡ {n_mod7} (mod 7):")
        for cn_mod7 in [0, 1, 2, 3, 4, 5, 6]:
            count = counter.get(cn_mod7, 0)
            pct = 100 * count / len(transitions[n_mod7]) if transitions[n_mod7] else 0
            if count > 0:
                print(f"    → C(n) ≡ {cn_mod7} (mod 7): {count} times ({pct:.1f}%)")
    print()

    # Test on n ≡ 3 (mod 8)
    print("For n ≡ 3 (mod 8), track trajectory mod 7:")
    print()

    # Multiple test cases
    test_cases = [27, 91, 155, 219, 283]

    for n in test_cases:
        traj = compute_trajectory(n)
        traj_mod7 = [v % 7 for v in traj]

        counter = Counter(traj_mod7)
        unique_mod7 = set(traj_mod7)

        print(f"n = {n}:")
        print(f"  Mod 7 classes visited: {sorted(unique_mod7)}")
        print(f"  Persistent? {'YES' if len(unique_mod7) == 1 else 'NO'}")
    print()

    return None

# Combined analysis for n ≡ 3 (mod 8)
def combined_analysis():
    """
    For n ≡ 3 (mod 8), analyze trajectory under mod 3, 5, 7, 8 simultaneously
    to see if any modulus reveals useful structure
    """
    print("="*80)
    print("COMBINED MULTI-MODULUS ANALYSIS FOR n ≡ 3 (mod 8)")
    print("="*80)
    print()

    test_cases = [27, 91, 155]

    for n in test_cases:
        print(f"n = {n} (≡ 3 mod 8)")
        print()

        traj = compute_trajectory(n)[:30]  # first 30 steps

        print(f"  Step | Value    | mod 3 | mod 5 | mod 7 | mod 8")
        print(f"  -----|----------|-------|-------|-------|-------")
        for i, val in enumerate(traj):
            print(f"  {i:4d} | {val:8d} | {val%3:5d} | {val%5:5d} | {val%7:5d} | {val%8:5d}")

        print()

        # Check for patterns
        full_traj = compute_trajectory(n)

        print(f"  Full trajectory ({len(full_traj)} steps):")
        print(f"    Mod 3 classes: {sorted(set(v % 3 for v in full_traj))}")
        print(f"    Mod 5 classes: {sorted(set(v % 5 for v in full_traj))}")
        print(f"    Mod 7 classes: {sorted(set(v % 7 for v in full_traj))}")
        print(f"    Mod 8 classes: {sorted(set(v % 8 for v in full_traj))}")
        print()

        # Check if any modulus shows persistence
        persistent_mod3 = len(set(v % 3 for v in full_traj)) == 1
        persistent_mod5 = len(set(v % 5 for v in full_traj)) == 1
        persistent_mod7 = len(set(v % 7 for v in full_traj)) == 1
        persistent_mod8 = len(set(v % 8 for v in full_traj)) == 1

        print(f"  Persistence:")
        print(f"    Mod 3: {'YES ✓' if persistent_mod3 else 'NO ✗'}")
        print(f"    Mod 5: {'YES ✓' if persistent_mod5 else 'NO ✗'}")
        print(f"    Mod 7: {'YES ✓' if persistent_mod7 else 'NO ✗'}")
        print(f"    Mod 8: {'YES ✓' if persistent_mod8 else 'NO ✗'}")
        print()
        print("-" * 80)
        print()

# Check what happens for n ≡ 3 (mod 8) specifically
def analyze_n_3_mod_8_under_mod_3():
    """
    Specific analysis: If n ≡ 3 (mod 8), what can we say about trajectory mod 3?

    n ≡ 3 (mod 8) means n = 8k + 3
    What is 8k + 3 (mod 3)?
    8k + 3 ≡ 2k + 0 ≡ 2k (mod 3)

    So n ≡ 3 (mod 8) can be:
    - n ≡ 0 (mod 3) if k ≡ 0 (mod 3): n = 3, 27, 51, ...
    - n ≡ 2 (mod 3) if k ≡ 1 (mod 3): n = 11, 35, 59, ...
    - n ≡ 1 (mod 3) if k ≡ 2 (mod 3): n = 19, 43, 67, ...
    """
    print("="*80)
    print("SPECIAL ANALYSIS: n ≡ 3 (mod 8) under MOD 3")
    print("="*80)
    print()

    print("Mathematical insight:")
    print("  n ≡ 3 (mod 8) means n = 8k + 3")
    print("  Under mod 3: 8k + 3 ≡ 2k (mod 3)")
    print()
    print("  So n ≡ 3 (mod 8) splits into:")
    print("    n ≡ 0 (mod 3) when k ≡ 0 (mod 3): n ∈ {3, 27, 51, 75, ...}")
    print("    n ≡ 2 (mod 3) when k ≡ 1 (mod 3): n ∈ {11, 35, 59, 83, ...}")
    print("    n ≡ 1 (mod 3) when k ≡ 2 (mod 3): n ∈ {19, 43, 67, 91, ...}")
    print()

    # Test each subclass
    for target_mod3 in [0, 1, 2]:
        print(f"Testing n ≡ 3 (mod 8) AND n ≡ {target_mod3} (mod 3):")

        # Find examples
        examples = []
        for n in range(3, 500, 8):
            if n % 3 == target_mod3:
                examples.append(n)
                if len(examples) >= 5:
                    break

        print(f"  Examples: {examples}")

        # For first example, show C(n) mod 3
        if examples:
            n = examples[0]
            cn = collatz(n)
            print(f"  C({n}) = {cn}")
            print(f"  C({n}) ≡ {cn % 3} (mod 3)")

        print()

if __name__ == "__main__":
    print()
    print("ALTERNATIVE MODULAR ARITHMETIC ANALYSIS")
    print("Question: Do mod 3, 5, or 7 reveal useful structure for n ≡ 3 (mod 8)?")
    print()

    analyze_mod_3()
    print()

    analyze_mod_5()
    print()

    analyze_mod_7()
    print()

    combined_analysis()

    analyze_n_3_mod_8_under_mod_3()

    print("="*80)
    print("SUMMARY AND CONCLUSIONS")
    print("="*80)
    print()
    print("Will be added after reviewing the results...")
    print()
