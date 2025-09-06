# PyPI Link Formatting Requirements for Code/README.md

## CRITICAL: Code/README.md Must Use Full GitHub URLs

The Code/README.md file serves as the front page for https://pypi.org/project/model-checker/ and **MUST use full GitHub URLs for ALL links** - no exceptions.

## Why This Matters

- **PyPI cannot resolve relative links** - they will appear broken to users
- **Users cannot navigate** to files outside the package from PyPI
- **Broken links harm credibility** and user experience

## Link Formatting Rules

### For Code/README.md (PyPI Display)

**EVERY link in Code/README.md must be a full GitHub URL:**

#### ✅ CORRECT - Full GitHub URLs (REQUIRED):
```markdown
[Technical Docs](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)
[Development Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/DEVELOPMENT.md)
[Theory Library](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)
[Theory Comparison Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/usage/COMPARE_THEORIES.md)
```

#### ❌ INCORRECT - Relative Links (NEVER USE in Code/README.md):
```markdown
[Technical Docs](docs/README.md)                    # BROKEN on PyPI
[Development Guide](../Docs/DEVELOPMENT.md)         # BROKEN on PyPI
[Theory Library](src/model_checker/theory_lib/)     # BROKEN on PyPI
[Theory Comparison Guide](../Docs/usage/COMPARE_THEORIES.md)  # BROKEN on PyPI
```

### For Other Documentation Files
- Other files in maintenance/, CLAUDE.md, and docs/ can use relative links
- These files are not displayed on PyPI and benefit from working relative navigation

## Current Full Hyperlinks in Code/README.md

The following links are currently using full hyperlinks correctly:
- Line 245: Theory Comparison Guide -> https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/usage/COMPARE_THEORIES.md
- Line 249: GitHub Repository -> https://github.com/benbrastmckie/ModelChecker
- Line 250: Development Guide -> https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/DEVELOPMENT.md
- Line 251: Theory Documentation -> https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib
- Line 252: Academic Background -> http://www.benbrastmckie.com/research#access
- Line 267-268: Citation links
- Line 272: LICENSE link
- Line 275-277: Support links

## Exception: Top Navigation Links

The top navigation links (lines 3, 282) use relative paths:
```markdown
[← Back to Project](../README.md) | [General Docs →](../Docs/README.md) | [Technical Docs →](docs/README.md)
```

These may need to be converted to full hyperlinks or removed for PyPI display, depending on requirements.

## Checking for Compliance

Run this command to find any relative links in Code/README.md:
```bash
grep -n '\](\.\./\|\](docs/\|\](src/' Code/README.md
```

If this returns any results, those links MUST be converted to full GitHub URLs.

## Common Link Patterns

### Navigation Links
```markdown
# Top/Bottom of Code/README.md
[← Back to Project](https://github.com/benbrastmckie/ModelChecker)
[General Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/README.md)
[Technical Docs →](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/docs/README.md)
```

### Documentation Links
```markdown
# Links to docs outside Code/ directory
[Development Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/DEVELOPMENT.md)
[Theory Comparison Guide](https://github.com/benbrastmckie/ModelChecker/blob/master/Docs/usage/COMPARE_THEORIES.md)

# Links to docs inside Code/ directory  
[API Documentation](https://github.com/benbrastmckie/ModelChecker/blob/master/Code/src/model_checker/README.md)
[Theory Library](https://github.com/benbrastmckie/ModelChecker/tree/master/Code/src/model_checker/theory_lib)
```

### External Links
```markdown
# These can remain as-is
[Academic Background](http://www.benbrastmckie.com/research#access)
[Journal Article](https://link.springer.com/article/10.1007/s10992-025-09793-8)
```

## Maintenance Checklist

When updating Code/README.md:
- [ ] Check ALL links use full GitHub URLs (except external non-GitHub links)
- [ ] Run the grep command above to verify no relative links remain
- [ ] Test that links work by visiting them in a browser
- [ ] Remember this requirement when copying content from other docs
- [ ] Update this document if new link patterns emerge

## Why Only Code/README.md?

- **Code/README.md** = PyPI front page → needs full URLs
- **All other files** = GitHub navigation → can use relative links for easier maintenance