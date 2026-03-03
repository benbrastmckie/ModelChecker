# Boneyard - Archived Code

This directory contains code that has been retired from active use but preserved for historical reference.

## Contents

### theory_lib/exclusion/

**Archived**: 2026-03-03

The Exclusion semantic theory - a fine-grained truthmaker semantics implementation.
Archived as part of codebase cleanup; the Logos theory now serves as the primary
truthmaker semantics implementation.

### theory_lib/imposition/

**Archived**: 2026-03-03

The Imposition semantic theory - an alternative fine-grained truthmaker semantics
with different constraint handling. Archived as part of codebase cleanup.

## Restoration

To restore an archived component:

1. Move the directory back to its original location
2. Update `theory_lib/__init__.py` to add the theory to `AVAILABLE_THEORIES`
3. Restore any removed test files and notebook templates
4. Run the full test suite to verify integration

See git history for the exact changes made during archival.

## Notes

- These theories may have outdated imports or dependencies
- No active maintenance is performed on archived code
- Use git history to trace the full implementation details
