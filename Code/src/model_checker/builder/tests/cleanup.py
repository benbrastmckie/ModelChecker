#!/usr/bin/env python3
"""
Cleanup script for builder test suite.

This script removes identified cruft and performs basic cleanup tasks.
Run with --dry-run to see what would be done without making changes.
"""
import os
import sys
import argparse
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description="Clean up builder test suite")
    parser.add_argument('--dry-run', action='store_true', 
                        help="Show what would be done without making changes")
    args = parser.parse_args()
    
    # Get test directory
    test_dir = Path(__file__).parent
    
    # Files to remove
    files_to_remove = [
        test_dir / "migrate_tests.py",
        test_dir / "test_refactor_baseline.py",
    ]
    
    # Check baseline directory usage
    baseline_dir = test_dir / "baseline"
    baseline_files_used = check_baseline_usage(test_dir, baseline_dir)
    
    print("Builder Test Suite Cleanup")
    print("=" * 50)
    
    # Remove identified cruft
    print("\n1. Removing cruft files:")
    for file_path in files_to_remove:
        if file_path.exists():
            if args.dry_run:
                print(f"   [DRY RUN] Would remove: {file_path.name}")
            else:
                file_path.unlink()
                print(f"   ✓ Removed: {file_path.name}")
        else:
            print(f"   - Already gone: {file_path.name}")
    
    # Report on baseline files
    print("\n2. Baseline directory analysis:")
    if baseline_files_used:
        print(f"   ✓ Baseline files are used in tests - keeping")
        for file, used_in in baseline_files_used.items():
            print(f"     - {file} used in: {', '.join(used_in)}")
    else:
        print(f"   ⚠ Baseline files appear unused")
        if args.dry_run:
            print(f"   [DRY RUN] Would remove baseline directory")
        else:
            print(f"   Consider removing baseline directory manually")
    
    # Check for other potential improvements
    print("\n3. Additional findings:")
    
    # Large test files that could be split
    large_files = []
    for test_file in test_dir.glob("test_*.py"):
        line_count = len(test_file.read_text().splitlines())
        if line_count > 300:
            large_files.append((test_file.name, line_count))
    
    if large_files:
        print("   Large test files that could be split:")
        for name, lines in sorted(large_files, key=lambda x: x[1], reverse=True):
            print(f"     - {name}: {lines} lines")
    
    # Duplicate test patterns
    print("\n   Test files with similar names (consider consolidating):")
    related_groups = [
        ["test_runner_extraction.py", "test_comparison_extraction.py", 
         "test_translation_extraction.py"],
        ["test_build_module_interactive.py", "test_cli_interactive_integration.py"],
        ["test_edge_cases.py", "test_generated_projects.py", 
         "test_integration_workflow.py"],
    ]
    
    for group in related_groups:
        existing = [f for f in group if (test_dir / f).exists()]
        if len(existing) > 1:
            print(f"     - {', '.join(existing)}")
    
    print("\n4. Recommendations:")
    print("   - Update tests/README.md to remove references to deleted files")
    print("   - Consider implementing improvements from improvements.md")
    print("   - Run pytest to ensure all tests still pass after cleanup")
    
    if args.dry_run:
        print("\n[DRY RUN] No changes were made. Run without --dry-run to apply changes.")


def check_baseline_usage(test_dir, baseline_dir):
    """Check if baseline files are used in any tests."""
    baseline_files = list(baseline_dir.glob("*.txt"))
    usage = {}
    
    for test_file in test_dir.glob("test_*.py"):
        content = test_file.read_text()
        for baseline_file in baseline_files:
            if baseline_file.name in content or str(baseline_file) in content:
                if baseline_file.name not in usage:
                    usage[baseline_file.name] = []
                usage[baseline_file.name].append(test_file.name)
    
    return usage


if __name__ == "__main__":
    main()