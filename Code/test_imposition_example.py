from model_checker.theory_lib.imposition import get_examples

# Get the example range
examples = get_examples()

# Print the first countermodel example
print("Available examples:")
for key in list(examples.keys())[:5]:
    print(f"  - {key}")

# Show a specific example
test_case = examples.get('cf_mp')
if test_case:
    print(f"\nExample 'cf_mp': {test_case}")