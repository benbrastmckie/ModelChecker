# Implementation Plan: Fix TestPyPI Trusted Publisher + One-Glance OIDC Diagnostics

- **Task**: 161 - Fix TestPyPI trusted-publisher registration and make future OIDC mismatches diagnosable in one glance
- **Status**: [IMPLEMENTING]
- **Effort**: 1.25 hours (agent-side: 0.75h; user-side gates: 0.5h plus CI wall-clock)
- **Dependencies**: None (this task BLOCKS `harden_release_ci_testpypi_gate`, which declares it as a dependency)
- **Research Inputs**: specs/161_fix_testpypi_trusted_publisher/reports/01_fix-testpypi-trusted-publisher.md
- **Artifacts**: plans/01_fix-testpypi-trusted-publisher.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, pr-prohibition.md
- **Type**: python
- **Lean Intent**: false

## Overview

TestPyPI publishing currently fails with `invalid-publisher` because no trusted publisher is
registered for `model-checker` on test.pypi.org. Exactly one part of the fix is
agent-authorable: an additive OIDC-claims diagnostic step in the `publish-testpypi` job of
`.github/workflows/release.yml`, so that a claims/registration mismatch is readable at a glance
in a clearly labeled step rather than buried in the upload step's failure output. The
registration itself and its only true verification (a real `v*` tag push) are user-only gates.
Definition of done, agent-side: the diagnostic step is committed, statically validated, and
audited to leak nothing; the two user gates are explicitly recorded for the user to execute.

### Research Integration

Findings from `reports/01_fix-testpypi-trusted-publisher.md` that this plan treats as ground
truth and does not re-derive:

- **Audience differs by index**: `https://test.pypi.org/_/oidc/audience` returns
  `{"audience":"testpypi"}`; `https://pypi.org/_/oidc/audience` returns `{"audience":"pypi"}`.
  These are different strings; `pypi` is wrong for the `publish-testpypi` job.
- **Mechanism is `curl` + `jq`, not `actions/github-script`**: every existing step in
  `release.yml` is plain bash, and GitHub's own reference tool `github/actions-oidc-debugger`
  uses exactly this recipe (mint via `$ACTIONS_ID_TOKEN_REQUEST_URL&audience=...`, `jq -r
  '.value'`, split the JWT on `.`, base64url-decode the payload, re-pipe through `jq`).
- **No automatic masking**: `ACTIONS_ID_TOKEN_REQUEST_TOKEN` and the minted JWT are
  runtime-generated, not registered `secrets.*` values, so GitHub does NOT mask them in logs.
  The `jq` whitelist filter is therefore the actual protection, not a convenience.
- **Upstream already owns the vocabulary**: `pypa/gh-action-pypi-publish`'s `oidc-exchange.py`
  prints `sub`, `repository`, `repository_owner`, `repository_owner_id`, `workflow_ref`,
  `job_workflow_ref`, `ref`, `environment` prefaced by "The claims rendered below are for
  debugging purposes only. You should not use them to configure a trusted publisher unless they
  already match your expectations." The new step reuses this vocabulary and framing rather than
  inventing a parallel one. What this task adds is not new data but its one-glance-ability.
- **Registration field values** (user gate): Owner `benbrastmckie`, Repository name
  `ModelChecker`, Workflow name `release.yml` (the literal filename, NOT the display name
  `Release`), Environment name `testpypi` (must not be left blank).
- **Authoritative ownership signal**: the Maintainers list on
  `https://test.pypi.org/project/model-checker/`, NOT the self-declared `author_email` metadata
  in the uploaded 0.1 package.
- **Base64 padding**: raw JWT base64url payloads are often missing `=` padding; a hardened
  implementation pads to a multiple of 4 before decoding, as both upstream `extract_claims` and
  the `actions-oidc-debugger` recipe do.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No ROADMAP.md consulted for this task (no `roadmap_path` provided).

## Goals & Non-Goals

**Goals**:
- Add one additive, diagnostic-only step to the `publish-testpypi` job that prints the four
  decoded OIDC claims (`sub`, `repository`, `workflow_ref`, `environment`) before the upload
  step runs, using the upstream claim vocabulary and disclaimer.
- Guarantee the step can never fail the job (step-level `continue-on-error: true`) and can never
  leak the request token or the raw JWT to any log, step output, env file, or artifact.
- Record the test.pypi.org trusted-publisher registration as an explicit, actionable user gate,
  including the authoritative ownership check and the fallback ladder.
- Keep the diff to `.github/workflows/release.yml` minimal and purely additive so
  `harden_release_ci_testpypi_gate` can re-read the file cleanly afterward.

**Non-Goals** (each belongs to the dependent task `harden_release_ci_testpypi_gate`; this plan
MUST NOT contain a phase for any of them):
- Removing or weakening the job-level `continue-on-error: true` at `.github/workflows/release.yml:147`.
- Adding a `verify-testpypi` install-and-smoke-test job.
- Adding preflight assertions or human confirmation gates to the release workflow.
- Anything else that promotes TestPyPI from soft canary to a real gate.

Additional non-goals for this task specifically:
- No agent attempt to log into, register on, upload to, or otherwise touch test.pypi.org.
- No `git push`, `git tag`, `/tag`, `/merge`, or twine upload by any agent (per
  `.claude/rules/pr-prohibition.md`).
- No change to `publish-pypi`, `build`, or any other job; no change to the `dist` artifact.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Raw JWT or `ACTIONS_ID_TOKEN_REQUEST_TOKEN` reaches an unmasked job log | H | L | `jq` whitelist filter is the sole stdout path; explicit leak audit in Phase 1 verification greps for every forbidden sink (`echo "$JWT"`, `$GITHUB_OUTPUT`, `$GITHUB_ENV`, `upload-artifact`) |
| Diagnostic step failure fails the `publish-testpypi` job | M | L | Step-level `continue-on-error: true`, distinct from the job-level flag on line 147; renders as a yellow triangle rather than a red X |
| Wrong audience (`pypi` instead of `testpypi`) yields a token that never matches | M | L | Audience resolved at runtime from `https://test.pypi.org/_/oidc/audience`, mirroring upstream, with a hardcoded `testpypi` fallback |
| Diff surface collides with `harden_release_ci_testpypi_gate` | M | M | Single additive insertion at one point in the job's `steps:` list; zero modified or deleted lines elsewhere; verified by `git diff --stat` in Phase 1 |
| Unpadded base64url payload fails to decode on the runner | L | M | Explicit `tr '_-' '/+'` plus pad-to-multiple-of-4 loop before `base64 -d`; decode pipeline replayed locally against a synthetic payload |
| User's TestPyPI account holds no role on the existing `model-checker` project | H | M | Phase 2 carries the full fallback ladder from the research report; ownership judged by the project page's Maintainers list, not package metadata |
| Agent marks the task done without the registration actually working | M | M | Phase 3 is a user-only verification gate; agent-side "done" is explicitly defined as the committed workflow change plus static checks, never a green CI run |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1, 2 |

Phases within the same wave can execute in parallel. Phase 1 is agent work; Phase 2 is user
work; they are genuinely independent and may proceed concurrently. Phase 3 requires both.

### Phase 1: Add OIDC-claims diagnostic step to `publish-testpypi` [COMPLETED]

**Goal**: `.github/workflows/release.yml` gains one additive, diagnostic-only step in the
`publish-testpypi` job that prints the four decoded OIDC claims before the upload step, cannot
fail the job, and leaks nothing.

**AGENT-AUTHORABLE.** This is the only phase an implementation dispatch executes.

**Tasks**:
- [x] Read the current `publish-testpypi` job (`.github/workflows/release.yml`, job begins at
      line 136; `steps:` at line 149; upload step `Publish to TestPyPI` at line 156). Re-derive
      the line numbers at implementation time rather than trusting these.
- [x] Insert a new step as the FIRST entry of the job's `steps:` list — immediately after
      `steps:` and before `- name: Download distribution artifact`. This satisfies the "before
      the `pypa/gh-action-pypi-publish` upload step" requirement and additionally surfaces the
      claims even if the artifact download fails or a future precondition prevents the upload
      step from running at all.
- [x] Author the step to this shape (adapt indentation to the file's existing 4-space
      step indentation; do not reformat surrounding YAML):

```yaml
    # Diagnostic only -- never a gate. Prints the OIDC claims test.pypi.org
    # matches a trusted publisher against, so an `invalid-publisher` rejection
    # is readable at a glance instead of by expanding the upload step's log.
    # Mirrors the claim vocabulary and "debugging purposes only" framing of
    # pypa/gh-action-pypi-publish's own oidc-exchange.py.
    #
    # SECURITY: ACTIONS_ID_TOKEN_REQUEST_TOKEN and the minted JWT are generated
    # at runtime and are NOT covered by GitHub's automatic secret masking. The
    # jq whitelist below is the only thing keeping them out of the log: neither
    # value is ever echoed, and neither is written to $GITHUB_OUTPUT,
    # $GITHUB_ENV, or an artifact.
    - name: Print OIDC claims (diagnostic only)
      continue-on-error: true
      env:
        # Kept in sync with the `repository-url` of the publish step below.
        OIDC_HOST: test.pypi.org
      run: |
        set -euo pipefail
        AUDIENCE="$(curl -sS "https://${OIDC_HOST}/_/oidc/audience" \
          | jq -r '.audience' || echo '')"
        if [ -z "${AUDIENCE}" ] || [ "${AUDIENCE}" = "null" ]; then
          AUDIENCE=testpypi
        fi
        echo "OIDC audience: ${AUDIENCE}"
        JWT="$(curl -sS \
          -H "Authorization: bearer ${ACTIONS_ID_TOKEN_REQUEST_TOKEN}" \
          "${ACTIONS_ID_TOKEN_REQUEST_URL}&audience=${AUDIENCE}" \
          | jq -r '.value')"
        PAYLOAD="$(printf '%s' "${JWT}" | cut -d. -f2 | tr '_-' '/+')"
        while [ $(( ${#PAYLOAD} % 4 )) -ne 0 ]; do PAYLOAD="${PAYLOAD}="; done
        echo "The claims below are for debugging purposes only. Do not use them"
        echo "to configure a trusted publisher unless they already match your"
        echo "expectations."
        printf '%s' "${PAYLOAD}" | base64 -d \
          | jq '{sub, repository, workflow_ref, environment}'
```

- [x] Confirm the deliberate decisions below are preserved verbatim, since each is a
      research-backed choice rather than an incidental detail:
  - **Audience is resolved, not hardcoded** (research section B option (ii)): the `curl` against
    `https://test.pypi.org/_/oidc/audience` mirrors what upstream `oidc-exchange.py` itself does
    and will not go stale if TestPyPI changes its audience string. The `testpypi` literal
    survives only as a fallback for a failed or malformed fetch. The *host* stays hardcoded and
    is deliberately commented as being in sync with the publish step's own hardcoded
    `repository-url: https://test.pypi.org/legacy/` — deriving the host would require a
    job-level variable and widen the diff for no diagnostic gain.
  - **`|| echo ''` inside the audience command substitution** is load-bearing: with
    `set -euo pipefail`, a `curl` failure would otherwise abort the step before the fallback
    `if` could run, making the fallback unreachable.
  - **`set -euo pipefail` is intentional** (not `set -uo`): a mint failure should fail the step
    loudly — which under step-level `continue-on-error: true` renders as a yellow triangle,
    itself useful signal — rather than printing garbage from a half-completed pipeline.
  - **`continue-on-error: true` at step level** (6-space indent, a sibling of `name:`/`run:`)
    is a distinct YAML attribute from the job-level flag at line 147 and must not be confused
    with or substituted for it.
  - **Only four claims are printed.** Upstream renders a fuller set; the four here are the
    minimum that diagnoses every registration-field mismatch and keeps the whitelist tight.
- [x] Verify the job's `permissions: id-token: write` (line 142) is already present — it is, and
      it must NOT be added again or moved.
- [x] Commit the change (`task 161: add OIDC claims diagnostic step to publish-testpypi`). Do
      NOT push, tag, or open a PR.

**Timing**: 45 minutes

**Depends on**: none

**Verification Tier**: local

Rationale for `local`: the edit is confined to one file with no externally visible signature
change and no Python/import surface. Its acknowledged blind spot — that a workflow's real
behavior is only observable when GitHub Actions runs it — is exactly what Phase 3 (tier `full`,
user-only) covers, and is unreachable by any agent under `.claude/rules/pr-prohibition.md`.

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts (a) exactly one file is modified,
`.github/workflows/release.yml`; (b) the change is purely additive — zero deleted or modified
pre-existing lines; (c) the four claim names `sub`, `repository`, `workflow_ref`, `environment`
are each present in the JWT payload GitHub mints for this job. Confirm (a) and (b) at
implementation time with `git diff --stat` and `git diff -- .github/workflows/release.yml`
(every diff line must be a `+`, apart from context and the hunk header). (c) is confirmable only
at Phase 3 and is carried forward as an open hypothesis; if any claim is absent, `jq` renders it
as `null` rather than failing, so the step degrades visibly rather than breaking.

**Files to modify**:
- `.github/workflows/release.yml` - insert one step at the head of the `publish-testpypi` job's
  `steps:` list. No other job, key, or line touched.

**Verification** (all agent-executable without pushing):
- [x] YAML still parses:
      `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/release.yml')); print('ok')"`
- [x] The new step's `run:` body is valid bash. Extract it and check syntax, e.g. a `python3`
      snippet that loads the YAML, selects
      `jobs['publish-testpypi']['steps']` by `name == 'Print OIDC claims (diagnostic only)'`,
      writes its `run` value to the scratchpad, then `bash -n` on that file.
- [x] Decode pipeline replayed locally: build a synthetic base64url payload containing the four
      claims (deliberately without `=` padding), run the `tr` + pad-loop + `base64 -d` + `jq`
      portion against it in the scratchpad, and confirm stdout is exactly a JSON object with the
      four keys and nothing else. This exercises the padding fix without any real token.
- [x] Step-level flag present and job-level flag untouched:
      `python3` assertion that the new step dict has `continue-on-error: True`, AND
      `git diff -- .github/workflows/release.yml` shows no change at or near line 147.
- [x] Leak audit over the new step's text only:
  - `ACTIONS_ID_TOKEN_REQUEST_TOKEN` appears exactly once, and only inside the `curl`
    `Authorization: bearer` header.
  - No `echo`/`printf`/`cat` of `${JWT}` or `$ACTIONS_ID_TOKEN_REQUEST_TOKEN`; the only
    `printf '%s' "${JWT}"` occurrence pipes directly into `cut`.
  - Zero occurrences of `GITHUB_OUTPUT`, `GITHUB_ENV`, `GITHUB_STATE`, `upload-artifact`, or
    `::set-output` anywhere in the new step.
  - The only unfiltered stdout writes are the three fixed disclaimer lines and the
    `OIDC audience:` line — no variable interpolation of a secret-bearing value.
- [x] Diff is additive-only and single-file: `git diff --stat` names exactly
      `.github/workflows/release.yml` with 0 deletions.
- [x] Change is committed; working tree clean for this file.

---

### Phase 2: USER GATE - Register the trusted publisher on test.pypi.org [NOT STARTED]

**Goal**: A GitHub Actions trusted publisher for `model-checker` exists on test.pypi.org with
field values that exactly match this workflow's OIDC claims.

**USER-ONLY. NO AGENT STEP MAY ATTEMPT ANY PART OF THIS PHASE.** An implementation dispatch must
not log into test.pypi.org, must not attempt registration via API or browser automation, must
not upload with twine, and must not implement a workaround. If this phase is still open when
Phase 1 completes, the agent leaves it `[NOT STARTED]` (or `[BLOCKED]` with "awaiting user
action" as the reason) and reports it to the user; it is never a reason to mark the task
complete or to widen the workflow change.

**Tasks** (for the user):
- [ ] Log in at `https://test.pypi.org` — a fully separate account system from pypi.org. A
      pypi.org session does not carry over; a distinct TestPyPI account is required, and it must
      be that account's session used below.
- [ ] **Authoritative ownership check first**: open
      `https://test.pypi.org/project/model-checker/` and read the **Maintainers** list on the
      project page. That list shows the TestPyPI usernames actually holding a role. Compare it
      against your own TestPyPI username. Do NOT infer ownership from the `author_email` in the
      uploaded 0.1 package metadata — that is self-declared build-time metadata and is not proof
      of account control.
- [ ] If your account is on that list, go to `https://test.pypi.org/manage/projects/`, click
      **Manage** next to `model-checker`, then **Publishing** in the sidebar
      (`https://test.pypi.org/manage/project/model-checker/publishing/`).
- [ ] In the GitHub Actions publisher form, enter exactly:
  - **Owner**: `benbrastmckie`
  - **Repository name**: `ModelChecker`
  - **Workflow name**: `release.yml` — the literal filename, NOT the workflow's `name:` display
    string (`Release`). This is the most likely single typo.
  - **Environment name**: `testpypi` — nominally optional in PyPI's schema but functionally
    required here. It must match the job's `environment: testpypi`
    (`.github/workflows/release.yml:140`). Leaving it blank registers a publisher that matches
    only tokens carrying no environment claim; this workflow's token always carries
    `environment: testpypi`, so a blank field reproduces the same `invalid-publisher` error.
- [ ] Click **Add**. No token or secret is generated or copied; trust takes effect via OIDC
      matching on the next run, and there is no activation delay to wait out.
- [ ] Note on permission level: PyPI describes two collaborator roles — a Maintainer can upload
      releases, an Owner can manage the project and its collaborators. Publishing-settings edits
      are not explicitly documented as Owner-only, but "manage the project" is the closest fit
      and is the safe assumption. If the Publishing page is read-only or inaccessible for an
      account that DOES appear under "Your projects", that is itself the signal the account holds
      Maintainer, not Owner — take fallback branch 1 below.

**Fallback ladder** (if your account holds no role, or an insufficient one):
1. **Ask the existing owner to act.** Fastest and zero workflow risk. The owner either grants
   your TestPyPI account Owner (or a role permitting Publishing edits) via the project's
   Collaborators page, or simply registers the trusted publisher themselves using the exact
   field values above. Neither path needs any `release.yml` change. Plausibly the co-author
   recorded in the 0.1 `author_email`, but verify against the Maintainers list rather than
   assuming.
2. **Request ownership transfer via PyPI/TestPyPI support** if the owner is unreachable. File at
   `https://github.com/pypi/support` (the shared tracker Warehouse uses for both pypi.org and
   test.pypi.org). Two things to ask rather than assume: (a) PEP 541's abandonment/name-retention
   bar is written for production PyPI; whether TestPyPI support applies the same bar, a lighter
   one, or handles it case-by-case is undocumented — ask directly in the support issue. (b)
   Community reports describe TestPyPI's database as periodically pruned with stale accounts
   sometimes removed; unpredictable and not self-service, but context for why support may resolve
   this faster than the production-PyPI equivalent.
3. **LAST RESORT, requires explicit user sign-off — do not implement unprompted.** Publish the
   TestPyPI rehearsal under a different, currently-unclaimed project name via the ordinary
   pending-publisher flow (Account Settings -> Publishing -> "Add a pending publisher"), which
   does apply to a never-used name. Real cost to surface before choosing it: `publish-testpypi`
   and `publish-pypi` consume the SAME `dist` artifact (built once in `build`, downloaded by
   both — release.yml:129-134, 150-154, 171-175), and the package name is baked into that
   artifact's wheel/sdist metadata at build time. This is therefore not a `repository-url`-only
   change; it needs either a second TestPyPI-only build with an overridden project name, or
   accepting a rehearsal that verifies differently-named bytes than what reaches production
   PyPI — which weakens the rehearsal's value.

**Timing**: 15 minutes (branch 1); indeterminate for branches 2-3

**Depends on**: none

**Verification Tier**: prose

Rationale for `prose`: this phase modifies no repository file and has zero compile, elaboration,
or import surface — nothing in the tier ladder above `prose` has anything to act on. Its real
verification is deferred wholesale to Phase 3.

**Scope Hypothesis**: This phase assumes the user's TestPyPI account holds Owner (or at least
Publishing-capable) role on the existing `model-checker` project. Confirm by reading the
Maintainers list at `https://test.pypi.org/project/model-checker/` BEFORE attempting the form; if
the assumption fails, the fallback ladder above replaces the main task list and the effort
estimate no longer holds.

**Files to modify**: none. This phase touches no repository file.

**Verification**:
- [ ] The Publishing page for `model-checker` on test.pypi.org lists a GitHub Actions publisher
      with owner `benbrastmckie`, repository `ModelChecker`, workflow `release.yml`, environment
      `testpypi`.
- [ ] The GitHub Environment named `testpypi` exists under repository Settings -> Environments
      (already documented in `.github/RELEASE_SETUP.md`; confirm rather than create if present).
- [ ] True end-to-end confirmation is Phase 3 only.

---

### Phase 3: USER GATE - Verify on a real `v*` tag push [NOT STARTED]

**Goal**: The `publish-testpypi` job goes green on a real release run, and the diagnostic step's
printed claims are confirmed to match the registered publisher fields.

**USER-ONLY.** Per `.claude/rules/pr-prohibition.md`, `git push`, `git tag`, `/tag`, `/merge`,
and twine uploads are all user-only. An agent may author and commit the workflow change but may
never exercise it. The agent-side definition of done for this task is Phase 1's committed change
plus its static checks — never a green CI run.

**Tasks** (for the user):
- [ ] Push a `v*` tag (via `/tag` or manually) to trigger the Release workflow.
- [ ] Open the `Publish to TestPyPI` job and read the `Print OIDC claims (diagnostic only)` step
      first. Confirm the printed values:
  - `repository` is `benbrastmckie/ModelChecker`
  - `workflow_ref` contains `.github/workflows/release.yml`
  - `environment` is `testpypi`
  - `sub` is consistent with the above
- [ ] Compare each against the registered publisher fields from Phase 2. Any single mismatch
      names the exact field to correct — that one-glance comparison is the deliverable of this
      task.
- [ ] Confirm the `Publish to TestPyPI` upload step succeeds (no `invalid-publisher`) and the job
      is green rather than soft-failed.
- [ ] Confirm the diagnostic step logged NO raw token and NO raw JWT — only the audience line,
      the three disclaimer lines, and the four-key JSON object.

**Timing**: 15 minutes of user attention plus CI wall-clock

**Depends on**: 1, 2

**Verification Tier**: full

Rationale for `full`: this is the only point at which the change's runtime behavior is observable
at all — real OIDC minting, real claim values, real publisher matching. It is the ceiling tier
and defers nothing, which is precisely why Phase 1's `local` tier is safe.

**Files to modify**: none.

**Verification**:
- [ ] `publish-testpypi` is green (not soft-failed via the job-level `continue-on-error`).
- [ ] The diagnostic step's output is present, readable, and leak-free.
- [ ] If a mismatch is found, correct the registered publisher field on test.pypi.org (Phase 2)
      and re-run; a mismatch does NOT imply a `release.yml` change.

---

## Testing & Validation

Agent-side (Phase 1, no push required):
- [ ] `python3 -c "import yaml; yaml.safe_load(open('.github/workflows/release.yml'))"` succeeds.
- [ ] `bash -n` on the extracted `run:` body of the new step succeeds.
- [ ] Decode pipeline replayed against a synthetic unpadded base64url payload emits exactly the
      four whitelisted keys.
- [ ] Leak audit greps all pass (no `GITHUB_OUTPUT`/`GITHUB_ENV`/`GITHUB_STATE`/`upload-artifact`
      in the new step; token referenced exactly once, in the `Authorization` header only).
- [ ] Step-level `continue-on-error: true` present; job-level line 147 unchanged.
- [ ] `git diff --stat` shows one file, zero deletions.
- [ ] No non-goal crept in: `git diff` contains no `verify-testpypi`, no removal of line 147, no
      preflight assertion, no confirmation gate.

User-side (Phase 3):
- [ ] Real `v*` tag push with `publish-testpypi` green.

## Artifacts & Outputs

- `.github/workflows/release.yml` — one additive diagnostic step in the `publish-testpypi` job
  (the only file changed by this task).
- One commit: `task 161: add OIDC claims diagnostic step to publish-testpypi`.
- `specs/161_fix_testpypi_trusted_publisher/summaries/01_*-summary.md` — implementation summary,
  which MUST record both user gates as outstanding if they are.

## Rollback/Contingency

The change is a single additive YAML step with step-level `continue-on-error: true`; it cannot
fail the job and cannot affect the upload. To revert, delete the step (or
`git revert` the single commit) — nothing else depends on it and no other file changes.

If the trusted-publisher registration turns out to be unobtainable (Phase 2 fallback branches 2
and 3 both blocked), the diagnostic step remains independently valuable — it makes the mismatch
legible — and the `publish-testpypi` job continues to soft-fail exactly as it does today, since
the job-level `continue-on-error: true` on line 147 is deliberately left in place by this task.
Escalate the ownership question to the user rather than working around it.
