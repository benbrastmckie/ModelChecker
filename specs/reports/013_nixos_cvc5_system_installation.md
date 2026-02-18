# NixOS System-Wide CVC5 Installation Guide

## Metadata
- **Date**: 2025-10-02
- **Purpose**: System-wide CVC5 Python bindings installation for NixOS
- **Context**: Make CVC5 always available without per-project setup
- **Related**: [Report 012: CVC5 Feasibility Results](012_cvc5_feasibility_results.md)

## Problem

Current setup uses per-project `shell.nix` with:
- Python venv + pip-installed CVC5
- Manual `LD_LIBRARY_PATH` configuration
- Not available system-wide

**Goal**: Install CVC5 Python bindings system-wide in NixOS configuration.

## Solution: Add to NixOS Configuration

### Option 1: Python Environment with CVC5 (Recommended)

Add to your `/etc/nixos/configuration.nix`:

```nix
{ config, pkgs, ... }:

{
  environment.systemPackages = with pkgs; [
    # Create Python environment with CVC5
    (python312.withPackages (ps: with ps; [
      pip
      # Add other Python packages you commonly use
    ]))
  ];

  # Required for CVC5 Python bindings (C++ library dependency)
  environment.variables = {
    LD_LIBRARY_PATH = "${pkgs.stdenv.cc.cc.lib}/lib:$LD_LIBRARY_PATH";
  };
}
```

Then rebuild and install CVC5:
```bash
sudo nixos-rebuild switch
pip install --user cvc5
```

**Why this works**:
- System Python available everywhere
- `LD_LIBRARY_PATH` provides `libstdc++.so.6` for CVC5 C++ bindings
- User-level pip install works with system Python

### Option 2: Custom Python Package Overlay (Advanced)

If you want CVC5 fully managed by Nix, create an overlay:

**File**: `~/.config/nixpkgs/overlays/cvc5.nix`
```nix
self: super: {
  python312 = super.python312.override {
    packageOverrides = pySelf: pySuper: {
      cvc5 = pySuper.buildPythonPackage rec {
        pname = "cvc5";
        version = "1.3.1";

        src = pySuper.fetchPypi {
          inherit pname version;
          sha256 = "sha256-XXXXX";  # Get via: nix-prefetch-url --unpack pypi.org/...
        };

        buildInputs = with self; [
          stdenv.cc.cc.lib
        ];

        # Patch RPATH for native libraries
        postInstall = ''
          for lib in $out/lib/python*/site-packages/cvc5.libs/*.so*; do
            patchelf --set-rpath ${self.stdenv.cc.cc.lib}/lib $lib
          done
        '';
      };
    };
  };
}
```

Then in `configuration.nix`:
```nix
environment.systemPackages = with pkgs; [
  (python312.withPackages (ps: [ ps.cvc5 ]))
];
```

**Advantages**:
- Fully declarative (reproducible)
- No manual pip installation
- Proper dependency management

**Disadvantages**:
- More complex setup
- Requires maintaining overlay
- May break on CVC5 updates

### Option 3: Home Manager (User-level, Recommended for single user)

If you use Home Manager, add to `~/.config/home-manager/home.nix`:

```nix
{ config, pkgs, ... }:

{
  home.packages = with pkgs; [
    (python312.withPackages (ps: with ps; [
      pip
    ]))
    stdenv.cc.cc.lib
  ];

  home.sessionVariables = {
    LD_LIBRARY_PATH = "${pkgs.stdenv.cc.cc.lib}/lib:$LD_LIBRARY_PATH";
  };

  # Install CVC5 in activation script
  home.activation.installCVC5 = config.lib.dag.entryAfter ["writeBoundary"] ''
    ${pkgs.python312}/bin/pip install --user cvc5
  '';
}
```

Apply with:
```bash
home-manager switch
```

## Verification

After installation, test:

```bash
# Test Python can import CVC5
python3 -c "import cvc5; print('CVC5 version:', cvc5.__version__)"

# Expected output:
# CVC5 version: 1.3.1
```

## Recommended Approach

**For most users**: **Option 1** (System packages + user pip)

**Pros**:
- Simple, minimal configuration
- Easy to update CVC5 (`pip install --upgrade cvc5`)
- Works immediately

**Cons**:
- Not fully declarative (pip install separate from Nix)
- Requires manual install after NixOS rebuild

**For purists**: **Option 2** (Custom overlay)

**Pros**:
- Fully declarative and reproducible
- Managed entirely by Nix

**Cons**:
- Complex initial setup
- Maintenance overhead

**For single-user systems**: **Option 3** (Home Manager)

**Pros**:
- User-level, doesn't require sudo
- Automatic pip installation on activation
- Per-user isolation

**Cons**:
- Requires Home Manager
- Installation in activation script not idiomatic Nix

## Critical Configuration for ModelChecker

Whichever option you choose, ensure the CVC5 options are set in code:

```python
solver = cvc5.Solver()
solver.setLogic("ALL")
solver.setOption("produce-models", "true")
solver.setOption("mbqi", "true")        # CRITICAL for witness predicates
solver.setOption("enum-inst", "true")   # CRITICAL for witness predicates
```

Without `mbqi` and `enum-inst`, CVC5 will return "unknown" for witness predicate problems.

## Migration from shell.nix

Once system-wide installation is complete:

1. **Remove** `shell.nix` (no longer needed)
2. **Remove** `venv/` directory
3. **Update** documentation to reference system installation
4. **Verify** `test_bm_cm_1_cvc5.py` runs without shell:
   ```bash
   python3 test_bm_cm_1_cvc5.py
   ```

## Troubleshooting

### ImportError: libstdc++.so.6: cannot open shared object file

**Cause**: `LD_LIBRARY_PATH` not set

**Fix**: Ensure `environment.variables.LD_LIBRARY_PATH` includes `${pkgs.stdenv.cc.cc.lib}/lib`

### ModuleNotFoundError: No module named 'cvc5'

**Cause**: CVC5 not installed for current Python

**Fix**:
```bash
pip install --user cvc5
# Or with system pip:
sudo pip install cvc5
```

### nix-shell still needed?

**Answer**: No! System-wide installation removes need for `shell.nix`. You can delete it once CVC5 works system-wide.

## References

- [NixOS Manual: Python](https://nixos.org/manual/nixpkgs/stable/#python)
- [Home Manager Manual](https://nix-community.github.io/home-manager/)
- [CVC5 PyPI](https://pypi.org/project/cvc5/)
- [Report 012: CVC5 Feasibility Results](012_cvc5_feasibility_results.md)
