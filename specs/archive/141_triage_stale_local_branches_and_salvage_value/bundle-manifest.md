# Bundle Manifest: Task #141 Stale Branch Archive

**Archive location**: `/home/benjamin/branch-archive/ModelChecker/`

This is outside `/home/benjamin/Projects/ModelChecker` (not in the working tree, not tracked, and
not touched by any git operation on the repository) and outside `/tmp` (survives reboot and
tmpfs cleanup). All nine of the branches classified in
`reports/01_stale-branch-triage.md` are bundled here in full (`refs/heads/<branch>`, not a
`master..branch` range), so every bundle is self-contained and verifies standalone with no
prerequisites.

## Bundle Table

| Branch | Bundle filename | Tip SHA | Size (bytes) | SHA-256 |
|---|---|---|---|---|
| `bimodal_refactor` | `bimodal_refactor.bundle` | `274fa0e93478528e690197a535dbb3e053e551ef` | 17287260 | `44269adf2a3bd83515c3ca3bac4175499491387b44b3c17e9e2b99275f231b6e` |
| `feature/bimodal-cvc5-pilot` | `feature__bimodal-cvc5-pilot.bundle` | `222add956f4aed777da9baebfe4426dfdce52633` | 17449624 | `e5cc3f42494e195dc7658ae50ee35379c208100419452568892666498d149a98` |
| `feature/bimodal_witness` | `feature__bimodal_witness.bundle` | `4a65f5601ec77794417afee10655ea4a278bd571` | 17015883 | `6b54b3c9409d606f81f680cd1f73374eb3e43b5d2a239f1c32e5f38de127437d` |
| `feature/bimodal_witness_backup` | `feature__bimodal_witness_backup.bundle` | `399c9afbd9227f0fb1c6637b43f676aa8ba9036a` | 16924133 | `3a9eb8c864dd48693df3431502c35c0481895b58893d6f8dbd0eaba8f14008ff` |
| `feature/cvc5-feasibility-test` | `feature__cvc5-feasibility-test.bundle` | `26e0a067fd58048c89dace1f5784c6f4cbd1f4c7` | 17322391 | `db47053a9818281c54bb8e1c9d00a5133afab9f5081dbc3f887a8925d5948d6d` |
| `feature/quantifier-free-witnesses` | `feature__quantifier-free-witnesses.bundle` | `01635e4aa26e45f8e9ac436940b17c996aacd7d9` | 17322376 | `71957596e61185c3b1147486fb2422962a927c95594980b1fb9bb55d45c1cc1d` |
| `feature/witness-falsity-attempt` | `feature__witness-falsity-attempt.bundle` | `c89f53274bf6035f00a28bd3af559f85708ef8d3` | 17313266 | `e4a7fdde8a4642a96f7ff414f3a0dc7cfccf7458dd2a6cb9afb4e634886ecf12` |
| `new_claude` | `new_claude.bundle` | `814872a81b78d35d56fbe3d0c2fe3965ad2ab585` | 19486713 | `b3f0c1f97ec1f9bd9d1fba0501b2ab16f60b65f05d415925f8db7ea068cbff05` |
| `refactor/exclusion` | `refactor__exclusion.bundle` | `0b9ddd0509b9266a8e41f9fc9d336765f8bef44b` | 17215328 | `74d42cac5c4a86d04c9bd2ece5584b4db468ae28206bc7e16dc2edb822b5d768` |

Each bundle's contained head SHA was cross-checked against `git rev-parse refs/heads/<branch>`
via `git bundle list-heads` before deletion; all nine matched exactly (no MISMATCH).

## Verbatim `git bundle verify` Output (all nine)

```
--- /home/benjamin/branch-archive/ModelChecker/bimodal_refactor.bundle ---
/home/benjamin/branch-archive/ModelChecker/bimodal_refactor.bundle is okay
The bundle contains this ref:
274fa0e93478528e690197a535dbb3e053e551ef refs/heads/bimodal_refactor
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__bimodal-cvc5-pilot.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__bimodal-cvc5-pilot.bundle is okay
The bundle contains this ref:
222add956f4aed777da9baebfe4426dfdce52633 refs/heads/feature/bimodal-cvc5-pilot
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness_backup.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness_backup.bundle is okay
The bundle contains this ref:
399c9afbd9227f0fb1c6637b43f676aa8ba9036a refs/heads/feature/bimodal_witness_backup
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__bimodal_witness.bundle is okay
The bundle contains this ref:
4a65f5601ec77794417afee10655ea4a278bd571 refs/heads/feature/bimodal_witness
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle is okay
The bundle contains this ref:
26e0a067fd58048c89dace1f5784c6f4cbd1f4c7 refs/heads/feature/cvc5-feasibility-test
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__quantifier-free-witnesses.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__quantifier-free-witnesses.bundle is okay
The bundle contains this ref:
01635e4aa26e45f8e9ac436940b17c996aacd7d9 refs/heads/feature/quantifier-free-witnesses
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/feature__witness-falsity-attempt.bundle ---
/home/benjamin/branch-archive/ModelChecker/feature__witness-falsity-attempt.bundle is okay
The bundle contains this ref:
c89f53274bf6035f00a28bd3af559f85708ef8d3 refs/heads/feature/witness-falsity-attempt
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/new_claude.bundle ---
/home/benjamin/branch-archive/ModelChecker/new_claude.bundle is okay
The bundle contains this ref:
814872a81b78d35d56fbe3d0c2fe3965ad2ab585 refs/heads/new_claude
The bundle records a complete history.
The bundle uses this hash algorithm: sha1

--- /home/benjamin/branch-archive/ModelChecker/refactor__exclusion.bundle ---
/home/benjamin/branch-archive/ModelChecker/refactor__exclusion.bundle is okay
The bundle contains this ref:
0b9ddd0509b9266a8e41f9fc9d336765f8bef44b refs/heads/refactor/exclusion
The bundle records a complete history.
The bundle uses this hash algorithm: sha1
```

## Restore Recipe

To restore any one of the nine branches from its bundle (creates the local branch again; does not
touch `origin` in any way):

```bash
git fetch /home/benjamin/branch-archive/ModelChecker/<bundle-file> refs/heads/<branch>:refs/heads/<branch>
```

For example, to restore `feature/cvc5-feasibility-test`:

```bash
git fetch /home/benjamin/branch-archive/ModelChecker/feature__cvc5-feasibility-test.bundle \
  refs/heads/feature/cvc5-feasibility-test:refs/heads/feature/cvc5-feasibility-test
```
