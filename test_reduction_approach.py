#!/usr/bin/env python3
"""
Test the reduction approach for n ≡ 3 (mod 8)

User's question: Can we prove n ≡ 3 (mod 8) reduces to classes {1, 5, 7 mod 8}
in finite steps, then use existing theorems?

Tests:
1. When first descent occurs (C^k(n) < n), which class mod 8?
2. Do ALL descent events occur in proven classes {1, 5, 7 mod 8}?
3. Can we prove this pattern analytically?
"""

from collections import Counter

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

def test_first_descent_class():
    """
    For n ≡ 3 (mod 8), find first k where C^k(n) < n
    Check which class (mod 8) this value belongs to
    """
    print("="*80)
    print("TEST 1: FIRST DESCENT CLASS")
    print("="*80)
    print()
    print("Question: When C^k(n) < n for the first time, what is C^k(n) mod 8?")
    print()

    results = []

    for n in range(3, 1000, 8):  # n ≡ 3 (mod 8)
        traj = compute_trajectory(n)

        # Find first descent below n
        first_descent_step = None
        first_descent_value = None
        first_descent_class = None

        for k, val in enumerate(traj):
            if val < n:
                first_descent_step = k
                first_descent_value = val
                first_descent_class = val % 8
                break

        if first_descent_step is not None:
            results.append({
                'n': n,
                'step': first_descent_step,
                'value': first_descent_value,
                'class': first_descent_class,
                'in_proven': first_descent_class in {1, 5, 7}
            })

    # Analysis
    print(f"Sample size: {len(results)} values")
    print()

    # Distribution by class
    class_counter = Counter(r['class'] for r in results)
    print("First descent class distribution:")
    for cls in sorted(class_counter.keys()):
        count = class_counter[cls]
        pct = 100 * count / len(results)
        proven = "✓ PROVEN" if cls in {1, 5, 7} else "✗ UNPROVEN"
        print(f"  Class {cls} (mod 8): {count:3d} cases ({pct:5.1f}%) {proven}")
    print()

    # Proven vs unproven
    proven_count = sum(1 for r in results if r['in_proven'])
    unproven_count = len(results) - proven_count

    print(f"Summary:")
    print(f"  Proven classes {{1,5,7}}: {proven_count}/{len(results)} ({100*proven_count/len(results):.1f}%)")
    print(f"  Unproven class {{3}}: {unproven_count}/{len(results)} ({100*unproven_count/len(results):.1f}%)")
    print()

    # Examples of unproven class
    if unproven_count > 0:
        print(f"Examples where first descent is to class 3 (mod 8):")
        unproven_examples = [r for r in results if not r['in_proven']][:10]
        for r in unproven_examples:
            print(f"  n={r['n']}: C^{r['step']}({r['n']}) = {r['value']} ≡ {r['class']} (mod 8)")
        print()

    # Key finding
    if unproven_count == 0:
        print("🎉 KEY FINDING: ALL first descents occur in proven classes {1, 5, 7}!")
        print("   This would complete the analytical proof!")
    else:
        print(f"⚠️  KEY FINDING: {100*unproven_count/len(results):.1f}% of first descents")
        print(f"   occur in class 3 (mod 8), which is also unproven.")
        print("   This creates a circular dependency.")
    print()

    return results

def test_all_descent_events():
    """
    Track ALL descent events (where C^(k+1)(n) < C^k(n))
    Check if they always occur in proven classes
    """
    print("="*80)
    print("TEST 2: ALL DESCENT EVENTS")
    print("="*80)
    print()
    print("Question: When C^(k+1)(n) < C^k(n) (any descent), what class is C^k(n)?")
    print()

    descent_classes = []

    for n in range(3, 500, 8):  # n ≡ 3 (mod 8)
        traj = compute_trajectory(n)

        for k in range(len(traj) - 1):
            if traj[k+1] < traj[k]:  # Descent event
                from_value = traj[k]
                from_class = from_value % 8
                to_value = traj[k+1]
                to_class = to_value % 8

                descent_classes.append({
                    'n': n,
                    'from_value': from_value,
                    'from_class': from_class,
                    'to_value': to_value,
                    'to_class': to_class,
                    'from_proven': from_class in {1, 5, 7},
                    'to_proven': to_class in {1, 5, 7}
                })

    # Analysis
    print(f"Total descent events: {len(descent_classes)}")
    print()

    # From which classes do descents occur?
    from_counter = Counter(d['from_class'] for d in descent_classes)
    print("Descent events BY SOURCE class:")
    for cls in sorted(from_counter.keys()):
        count = from_counter[cls]
        pct = 100 * count / len(descent_classes)
        proven = "✓" if cls in {1, 5, 7} else "✗"
        print(f"  From class {cls} (mod 8): {count:4d} events ({pct:5.1f}%) {proven}")
    print()

    # To which classes do descents go?
    to_counter = Counter(d['to_class'] for d in descent_classes)
    print("Descent events BY TARGET class:")
    for cls in sorted(to_counter.keys()):
        count = to_counter[cls]
        pct = 100 * count / len(descent_classes)
        proven = "✓" if cls in {1, 5, 7} else "✗"
        print(f"  To class {cls} (mod 8): {count:4d} events ({pct:5.1f}%) {proven}")
    print()

    # Both proven?
    both_proven = sum(1 for d in descent_classes if d['from_proven'] and d['to_proven'])
    print(f"Descents where BOTH source and target are proven: {both_proven}/{len(descent_classes)} ({100*both_proven/len(descent_classes):.1f}%)")
    print()

def test_class_3_loop():
    """
    Special test: If we first descend to class 3 (mod 8), what happens?
    Does it then reduce to {1, 5, 7}?
    """
    print("="*80)
    print("TEST 3: CLASS 3 LOOP CHECK")
    print("="*80)
    print()
    print("Question: If first descent is to class 3, does it then reduce to {1,5,7}?")
    print()

    # Find cases where first descent is to class 3
    class_3_cases = []

    for n in range(3, 1000, 8):  # n ≡ 3 (mod 8)
        traj = compute_trajectory(n)

        # Find first descent below n
        for k, val in enumerate(traj):
            if val < n:
                if val % 8 == 3:
                    class_3_cases.append({
                        'n': n,
                        'first_descent_step': k,
                        'first_descent_value': val
                    })
                break

    print(f"Found {len(class_3_cases)} cases where first descent is to class 3 (mod 8)")
    print()

    if len(class_3_cases) > 0:
        print("Analyzing these cases:")
        for case in class_3_cases[:5]:
            n = case['n']
            m = case['first_descent_value']
            print(f"\n  n = {n} ≡ 3 (mod 8)")
            print(f"    First descent: C^{case['first_descent_step']}({n}) = {m} ≡ 3 (mod 8)")
            print(f"    Now we have m < n with m ≡ 3 (mod 8)")
            print(f"    This is the SAME problem! (circular)")

            # Check if m descends to proven class
            m_traj = compute_trajectory(m)
            for k, val in enumerate(m_traj):
                if val < m:
                    print(f"    m's first descent: C^{k}({m}) = {val} ≡ {val % 8} (mod 8)", end="")
                    if val % 8 in {1, 5, 7}:
                        print(" ✓ PROVEN")
                    else:
                        print(" ✗ UNPROVEN (class 3 again!)")
                    break
        print()

        print("PROBLEM: This creates a recursive dependency!")
        print("  To prove n ≡ 3 (mod 8), we need to prove m ≡ 3 (mod 8) first.")
        print("  But we can't use induction because m < n doesn't help with descent time.")
    print()

def analyze_theorem_d2_application():
    """
    Check: After C(n) for n ≡ 3 (mod 8), we get C(n) ≡ 1 or 5 (mod 8)
    Does C(n) always descend within 2 steps? (Theorem A says τ ≤ 2 for {1,5 mod 8})
    """
    print("="*80)
    print("TEST 4: THEOREM D.2 + THEOREM A APPLICATION")
    print("="*80)
    print()
    print("Theorem D.2: n ≡ 3 (mod 8) → C(n) ≡ 1 or 5 (mod 8)")
    print("Theorem A: m ≡ 1 or 5 (mod 8) → τ(m) ≤ 2")
    print()
    print("Question: Does this tell us anything about τ(n)?")
    print()

    results = []

    for n in range(3, 500, 8):  # n ≡ 3 (mod 8)
        cn = collatz(n)
        cn_class = cn % 8

        # Check Theorem D.2
        assert cn_class in {1, 5}, f"Theorem D.2 violated! C({n}) = {cn} ≡ {cn_class} (mod 8)"

        # Check if C(n) < n
        cn_descends_immediately = (cn < n)

        # Compute τ(C(n)) using Theorem A
        # Theorem A says τ(C(n)) ≤ 2
        # So C(n) reaches m < C(n) within 2 steps
        traj_from_cn = compute_trajectory(cn)
        tau_cn = None
        for k, val in enumerate(traj_from_cn):
            if val < cn:
                tau_cn = k
                break

        # What about τ(n)?
        traj_from_n = compute_trajectory(n)
        tau_n = None
        for k, val in enumerate(traj_from_n):
            if val < n:
                tau_n = k
                break

        results.append({
            'n': n,
            'cn': cn,
            'cn_class': cn_class,
            'cn_descends': cn_descends_immediately,
            'tau_cn': tau_cn,
            'tau_n': tau_n
        })

    # Analysis
    print(f"Sample: {len(results)} values")
    print()

    # How often does C(n) < n?
    immediate_descent = sum(1 for r in results if r['cn_descends'])
    print(f"Cases where C(n) < n: {immediate_descent}/{len(results)} ({100*immediate_descent/len(results):.1f}%)")
    print()

    # Relationship between τ(C(n)) and τ(n)
    print("Relationship: τ(n) vs τ(C(n))")
    print()
    print("  If C(n) < n:")
    print(f"    Then τ(n) = 1 (immediate descent)")
    print(f"    Happens in {immediate_descent} cases")
    print()
    print("  If C(n) ≥ n:")
    delayed = len(results) - immediate_descent
    print(f"    Then τ(n) > 1")
    print(f"    Happens in {delayed} cases ({100*delayed/len(results):.1f}%)")
    print(f"    Theorem A tells us τ(C(n)) ≤ 2")
    print(f"    But this doesn't bound τ(n)!")
    print()

    # Examples where C(n) > n
    print("Examples where C(n) ≥ n:")
    delayed_examples = [r for r in results if not r['cn_descends']][:5]
    for r in delayed_examples:
        print(f"  n={r['n']}: C(n)={r['cn']} ≡ {r['cn_class']} (mod 8), τ(C(n))={r['tau_cn']}, τ(n)={r['tau_n']}")
    print()

    print("CONCLUSION:")
    print("  Theorem D.2 + Theorem A tell us:")
    print("    • C(n) ≡ 1 or 5 (mod 8) [proven]")
    print("    • τ(C(n)) ≤ 2 [proven]")
    print("  But they DON'T tell us:")
    print("    • Whether C(n) < n")
    print("    • The value of τ(n)")
    print()
    print("  The problem: C(n) might be LARGER than n, so descent of C(n)")
    print("  doesn't guarantee descent of n.")
    print()

if __name__ == "__main__":
    print()
    print("REDUCTION APPROACH ANALYSIS")
    print("="*80)
    print()
    print("User's Question: Can we prove n ≡ 3 (mod 8) reduces to classes")
    print("                 {1, 5, 7 mod 8} in finite steps?")
    print()

    # Run tests
    test_first_descent_class()
    test_all_descent_events()
    test_class_3_loop()
    analyze_theorem_d2_application()

    print("="*80)
    print("FINAL SUMMARY")
    print("="*80)
    print()
    print("User's reduction approach is clever, but faces challenges:")
    print()
    print("1. ✅ GOOD: Theorem D.2 proves C(n) ≡ 1 or 5 (mod 8) after 1 step")
    print("2. ✅ GOOD: Theorems A and E prove descent for classes {1, 5, 7}")
    print("3. ❌ PROBLEM: C(n) might be > n, so we haven't descended yet")
    print("4. ❌ PROBLEM: Some cases first descend to class 3 (circular!)")
    print()
    print("The fundamental issue:")
    print("  - Reducing to a proven CLASS is easy (1 step via Theorem D.2)")
    print("  - Reducing to a proven class WITH DESCENT is hard (unbounded steps)")
    print()
    print("This is essentially still proving τ(n) < ∞, just rephrased.")
    print()
