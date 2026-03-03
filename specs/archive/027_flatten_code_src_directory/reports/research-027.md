# Research Report: Task #27

**Task**: 27 - Flatten code/src/ directory structure
**Started**: 2026-03-03T12:00:00Z
**Completed**: 2026-03-03T12:30:00Z
**Effort**: Large (significant refactoring with high risk)
**Dependencies**: None
**Sources/Inputs**: Codebase analysis, pyproject.toml, import pattern analysis
**Artifacts**: This research report
**Standards**: report-format.md

## Executive Summary

- **Scale**: 382 Python files in `code/src/model_checker/`, 811 references to `code/src/model_checker` across 132 files
- **Impact**: Would require changing package name from `model_checker` to direct imports, affecting all 300+ relative imports and external references
- **Risk Level**: HIGH - This is not a simple directory move but a fundamental package rename
- **Recommendation**: RECONSIDER the task scope - the current structure follows Python packaging best practices

## Context & Scope

The task proposes moving contents of `code/src/model_checker/` into `code/src/` to "eliminate unnecessary directory depth." This research analyzes the full scope of such a change.

### Current Structure

```
code/
├── src/
│   ├── model_checker/              # Main package (382 Python files)
│   │   ├── __init__.py            # Package initialization
│   │   ├── __main__.py            # CLI entry point
│   │   ├── builder/               # 20+ modules
│   │   ├── iterate/               # 15+ modules
│   │   ├── jupyter/               # 20+ modules
│   │   ├── models/                # 10+ modules
│   │   ├── output/                # 20+ modules
│   │   ├── settings/              # 5+ modules
│   │   ├── syntactic/             # 12+ modules
│   │   ├── theory_lib/            # 50+ modules (4 theories)
│   │   └── utils/                 # 15+ modules
│   └── model_checker.egg-info/    # Build metadata
├── tests/                         # External test directory
└── pyproject.toml                 # Package configuration
```

### Proposed Structure (Flattened)

```
code/
├── src/
│   ├── __init__.py                # Would need to become the package init
│   ├── __main__.py
│   ├── builder/
│   ├── iterate/
│   ├── jupyter/
│   ├── models/
│   ├── output/
│   ├── settings/
│   ├── syntactic/
│   ├── theory_lib/
│   └── utils/
├── tests/
└── pyproject.toml
```

## Findings

### 1. Import Analysis

#### 1.1 Absolute Imports from `model_checker`

**Count**: 162 occurrences across source files

Common patterns:
```python
from model_checker.theory_lib import logos
from model_checker.builder import BuildModule
from model_checker.utils import get_theory
from model_checker import Syntax, ModelConstraints
import model_checker
```

Files with most absolute imports:
- `jupyter/` directory - 40+ imports
- `builder/` directory - 30+ imports
- Test files - 80+ imports

#### 1.2 Relative Imports

**Count**: 300+ occurrences across 107 files

Common patterns:
```python
from .models import Model                    # Single-dot (same package)
from ..utils import bitvec_to_substates     # Double-dot (parent package)
from ...logos.semantic import LogosSemantics # Triple-dot (grandparent)
```

Relative import depth analysis:
- Single-dot (`.`): ~200 occurrences
- Double-dot (`..`): ~80 occurrences
- Triple-dot (`...`): ~20 occurrences

#### 1.3 External References

**Test files** (`code/tests/`): 50+ imports of `model_checker`
**Documentation** (`docs/`): 50+ references to import paths
**CLAUDE.md and .claude/**: 10+ references

### 2. Configuration Files Affected

#### 2.1 pyproject.toml (Critical)

```toml
[project.scripts]
model-checker = "model_checker.__main__:run"  # Entry point

[tool.setuptools]
package-dir = {"" = "src"}

[tool.setuptools.packages.find]
where = ["src"]

[tool.pytest.ini_options]
pythonpath = "src"
testpaths = ["src/model_checker/theory_lib"]
```

Changes required:
- Entry point would need to change
- `testpaths` would need updating
- Package discovery would fundamentally change

#### 2.2 MANIFEST.in

```
recursive-include src/model_checker/theory_lib README.md
recursive-include src/model_checker/jupyter README.md
```

All 7 `model_checker` path references would need updating.

#### 2.3 conftest.py (code/tests/conftest.py)

```python
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))
# Module cleanup references model_checker
if module.startswith('model_checker'):
```

### 3. Structural Considerations

#### 3.1 Why Current Structure Exists

The `code/src/model_checker/` pattern is the **standard Python packaging layout**:

1. **Namespace isolation**: Package name `model_checker` is the importable namespace
2. **Build compatibility**: Works with setuptools, pip, and PyPI
3. **Entry points**: CLI (`model-checker`) references `model_checker.__main__:run`
4. **Installed package**: When installed via pip, users `import model_checker`

#### 3.2 What Flattening Would Actually Mean

Flattening is NOT just moving files. It would:

1. **Change the package name** from `model_checker` to... what?
   - Option A: Keep `model_checker` but have it at `src/` level (unconventional)
   - Option B: Change imports to `from builder import ...` (breaks user code)
   - Option C: Create multiple top-level packages (complicates installation)

2. **Break the published PyPI package**
   - Current users do `from model_checker import get_theory`
   - This would require a major version bump (breaking change)

3. **Require 800+ file edits**
   - 382 Python source files
   - 132 files with path references
   - External documentation and configuration

### 4. Risk Assessment

| Risk | Severity | Likelihood | Impact |
|------|----------|------------|--------|
| Import breakage | High | Certain | All imports need updating |
| Test failures | High | Certain | 20 test directories affected |
| Documentation drift | Medium | High | 50+ doc references outdated |
| PyPI compatibility | High | Certain | Published package breaks |
| Build system failures | High | Likely | Entry points, discovery |
| User code breakage | High | Certain | External users affected |

### 5. Alternative Interpretations

#### 5.1 Maybe the Task Means Something Else?

Re-reading the task description:
> "Move contents of `code/src/model_checker/` into `code/src/`"

This could mean:
1. **(As analyzed)** Flatten the package structure
2. **OR** Just rename `model_checker` directory (cosmetic, same problems)
3. **OR** Move individual subpackages up one level (still breaks imports)

None of these interpretations avoid the fundamental issue: `model_checker` is the package name used everywhere.

#### 5.2 What Would Actually Reduce Directory Depth?

If the goal is "less nesting," alternatives that don't break imports:
1. **Do nothing**: Current structure is standard and works
2. **Flatten internal structure**: Move `theory_lib/logos/subtheories/*` up if needed
3. **Rename deep paths**: Within the package, not the package itself

## Recommendations

### Primary Recommendation: RECONSIDER THIS TASK

The described change would:
- Require 800+ file modifications
- Break the published PyPI package
- Break all user code that imports `model_checker`
- Violate Python packaging standards
- Provide minimal practical benefit

**The current `code/src/model_checker/` structure is correct and follows Python best practices.**

### If Task Must Proceed

If there is a compelling reason not captured here, the migration would require:

1. **Phase 1: Preparation**
   - Document all import locations (done in this research)
   - Create comprehensive test baseline
   - Decide on new package name/structure

2. **Phase 2: Configuration**
   - Update pyproject.toml entry points
   - Update MANIFEST.in paths
   - Update pytest configuration

3. **Phase 3: Source Migration**
   - Move files with atomic commit
   - Update all absolute imports (162 occurrences)
   - Update all relative imports (300+ occurrences)
   - Update test imports (80+ occurrences)

4. **Phase 4: Documentation**
   - Update all 50+ documentation references
   - Update CLAUDE.md and .claude/ files
   - Update README.md examples

5. **Phase 5: Verification**
   - Run full test suite
   - Verify package builds correctly
   - Test pip installation
   - Verify CLI entry point works

**Estimated effort**: 2-3 days of careful work with high regression risk

## Questions for Clarification

Before proceeding, please clarify:

1. **What problem is this solving?** The current structure follows Python standards.
2. **Is this related to a specific pain point?** Understanding the motivation might reveal a better solution.
3. **Is user-facing compatibility a concern?** Existing users import `model_checker`.
4. **Should this be deprioritized?** The effort-to-benefit ratio is very high.

## Appendix

### A. Files with Most Import Changes Required

1. `code/src/model_checker/__init__.py` - 20+ imports
2. `code/src/model_checker/__main__.py` - 5 imports
3. `code/tests/conftest.py` - module cleanup references
4. `code/tests/integration/*.py` - 30+ test files
5. `code/src/model_checker/jupyter/display.py` - 10+ imports
6. `code/src/model_checker/builder/example.py` - 12+ imports

### B. Search Commands Used

```bash
# Absolute imports
grep -r "from model_checker" code/src/ | wc -l  # 162

# Relative imports
grep -r "^from \." code/src/model_checker/ | wc -l  # 300+

# Path references
grep -r "code/src/model_checker" . | wc -l  # 811
```

### C. Key Configuration Snippets

**pyproject.toml entry point**:
```toml
[project.scripts]
model-checker = "model_checker.__main__:run"
```

**top_level.txt**:
```
model_checker
```

**pytest configuration**:
```toml
testpaths = ["src/model_checker/theory_lib"]
```
