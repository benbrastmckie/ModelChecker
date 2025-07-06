"""
Analyze the 5 countermodel cases to understand what makes them special.
"""

# The 5 countermodel cases from our exploration:
countermodel_cases = [
    {
        'name': 'Only Frame Constraints',
        'premises': [],
        'conclusions': [],
        'category': 'frame'
    },
    {
        'name': 'No Gaps', 
        'premises': [],
        'conclusions': ['(A \\\\univee \\\\exclude A)'],
        'category': 'frame'
    },
    {
        'name': 'Double Negation Introduction',
        'premises': ['A'],
        'conclusions': ['\\\\exclude \\\\exclude A'],
        'category': 'negation'
    },
    {
        'name': 'Double Negation Identity',
        'premises': [],
        'conclusions': ['(A \\\\uniequiv \\\\exclude \\\\exclude A)'],
        'category': 'negation'
    },
    {
        'name': 'EX_CM_1',
        'premises': [],
        'conclusions': ['\\\\exclude (A \\\\univee \\\\exclude A)'],
        'category': 'other'
    }
]

def analyze_countermodel_patterns():
    """Analyze what these countermodel cases tell us about exclusion logic."""
    
    print("="*80)
    print("ANALYSIS OF COUNTERMODEL CASES IN EXCLUSION LOGIC")
    print("="*80)
    
    print(f"\nThe 5 countermodel cases represent only 13.9% of all examples.")
    print(f"This suggests exclusion logic is surprisingly classical for most operators.")
    print(f"\nLet's examine what makes these cases special:\n")
    
    for i, case in enumerate(countermodel_cases, 1):
        print(f"{i}. {case['name']} ({case['category']})")
        if case['premises']:
            print(f"   Premises: {case['premises']}")
        else:
            print(f"   Premises: [none]")
        
        if case['conclusions']:
            print(f"   Conclusions: {case['conclusions']}")
        else:
            print(f"   Conclusions: [none]")
        
        # Analysis of what this reveals
        if case['name'] == 'Only Frame Constraints':
            print(f"   → INSIGHT: Even with no premises/conclusions, exclusion logic")
            print(f"     can have countermodels. This suggests the frame itself")
            print(f"     provides constraints that can be violated.")
            
        elif case['name'] == 'No Gaps':
            print(f"   → INSIGHT: The law of excluded middle (A ∨ ¬A) is NOT")
            print(f"     a theorem in exclusion logic! This is a major departure")
            print(f"     from classical logic.")
            
        elif case['name'] == 'Double Negation Introduction':
            print(f"   → INSIGHT: While ¬¬A ⊢ A (elimination) is valid,")
            print(f"     A ⊢ ¬¬A (introduction) is NOT. This asymmetry")
            print(f"     is crucial to understanding exclusion logic.")
            
        elif case['name'] == 'Double Negation Identity':
            print(f"   → INSIGHT: A ≡ ¬¬A is not a theorem, confirming")
            print(f"     that double negation is not fully equivalent to")
            print(f"     the original proposition in exclusion logic.")
            
        elif case['name'] == 'EX_CM_1':
            print(f"   → INSIGHT: ¬(A ∨ ¬A) has a countermodel, which")
            print(f"     makes sense given that (A ∨ ¬A) itself isn't")
            print(f"     a theorem (see 'No Gaps' above).")
        
        print()
    
    print("PATTERN ANALYSIS:")
    print("="*40)
    
    print(f"\n1. CLASSICAL OPERATORS ARE ROBUST:")
    print(f"   - All DeMorgan, distribution, absorption, and associativity laws hold")
    print(f"   - This suggests exclusion logic preserves classical structure")
    print(f"     for Boolean combinations")
    
    print(f"\n2. NEGATION IS THE KEY DIFFERENCE:")
    print(f"   - 2/6 negation examples have countermodels")
    print(f"   - The asymmetry in double negation is crucial")
    print(f"   - Law of excluded middle fails")
    
    print(f"\n3. FRAME-LEVEL CONSTRAINTS MATTER:")
    print(f"   - Even empty formulas can have interesting semantics")
    print(f"   - The frame structure itself imposes constraints")
    
    print(f"\n4. NON-CLASSICAL GAPS:")
    print(f"   - Excluded middle: ⊬ (A ∨ ¬A)")
    print(f"   - Double negation intro: A ⊬ ¬¬A")
    print(f"   - Double negation identity: ⊬ (A ≡ ¬¬A)")
    
    print(f"\n5. PRESERVED CLASSICAL LAWS:")
    print(f"   - Double negation elim: ¬¬A ⊢ A")
    print(f"   - All DeMorgan's laws")
    print(f"   - All distribution laws")
    print(f"   - All absorption laws")
    print(f"   - All associativity laws")

def compare_with_classical_logic():
    """Compare these results with what we'd expect in classical logic."""
    
    print(f"\n" + "="*80)
    print("COMPARISON WITH CLASSICAL LOGIC")
    print("="*80)
    
    classical_theorems = [
        ("Law of Excluded Middle", "⊢ (A ∨ ¬A)", "FAILS in exclusion logic"),
        ("Double Negation Introduction", "A ⊢ ¬¬A", "FAILS in exclusion logic"),
        ("Double Negation Identity", "⊢ (A ≡ ¬¬A)", "FAILS in exclusion logic"),
        ("Double Negation Elimination", "¬¬A ⊢ A", "HOLDS in exclusion logic"),
        ("DeMorgan's Laws", "Various forms", "ALL HOLD in exclusion logic"),
        ("Distribution Laws", "Various forms", "ALL HOLD in exclusion logic"),
        ("Absorption Laws", "Various forms", "ALL HOLD in exclusion logic"),
        ("Associativity Laws", "Various forms", "ALL HOLD in exclusion logic"),
    ]
    
    print(f"\nCLASSICAL vs EXCLUSION LOGIC COMPARISON:")
    print(f"{'-'*80}")
    
    for name, formula, status in classical_theorems:
        print(f"{name:25} | {formula:15} | {status}")
    
    print(f"\nKEY INSIGHT:")
    print(f"Exclusion logic appears to be a 'classical logic minus excluded middle'")
    print(f"It preserves most classical theorems but crucially fails on:")
    print(f"1. Law of excluded middle")
    print(f"2. Double negation introduction")
    print(f"3. Double negation identity")
    print(f"\nThis suggests exclusion logic might be a type of 'gap logic' where")
    print(f"propositions can be neither true nor false (gaps), but when they")
    print(f"are true or false, they behave classically.")

if __name__ == "__main__":
    analyze_countermodel_patterns()
    compare_with_classical_logic()