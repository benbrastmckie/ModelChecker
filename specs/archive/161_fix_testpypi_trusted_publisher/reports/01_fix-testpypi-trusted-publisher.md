# Research: Fix TestPyPI Trusted-Publisher Registration + One-Glance OIDC Diagnostics

## Scope

This report answers exactly the three questions posed by task 161: (A) the web-UI procedure for
registering a trusted publisher on an *existing* TestPyPI project plus ownership fallbacks, (B)
the correct pattern for minting/decoding the GitHub Actions OIDC token in-workflow for a
diagnostic print, and (C) whether upstream already prescribes a diagnostic idiom. It explicitly
does **not** cover promoting `publish-testpypi` to a hard gate, adding a `verify-testpypi`
install/smoke-test job, or any environment-protection changes — those belong to the dependent
task `harden_release_ci_testpypi_gate`.

## (A) Registering a trusted publisher on an existing TestPyPI project

### Confirmed procedure (existing project, not "pending publisher")

Source: `docs.pypi.org/trusted-publishers/adding-a-publisher/` (fetched directly).

1. Log in at **https://test.pypi.org** — this is a fully separate account system from
   pypi.org. A pypi.org login does not carry over; the user must have (or create) a distinct
   TestPyPI account, and it must be *that* account's session used below.
2. Go to `https://test.pypi.org/manage/projects/` and click **Manage** next to `model-checker`.
   The project only appears here if the logged-in account already holds a role (Owner or
   Maintainer) on it — if it's absent, the account has no role at all and the fallback branch
   below applies.
3. Click **Publishing** in the project's sidebar
   (`https://test.pypi.org/manage/project/model-checker/publishing/`).
4. Under the GitHub Actions publisher form, the *required* fields are:
   - **Owner**: `benbrastmckie`
   - **Repository name**: `ModelChecker`
   - **Workflow name**: `release.yml` — the literal filename, **not** the workflow's `name:`
     display string (`Release`). This is exactly failure mode (c) already named in the task
     description as the most-likely typo.
   - **Environment name** (optional per PyPI's schema, but functionally required here): `testpypi`
     — must exactly match the job's `environment: testpypi` (release.yml:140). Leaving it blank
     registers a publisher that only matches tokens carrying *no* environment claim; this
     workflow's OIDC token always carries `environment: testpypi`, so a blank field will not
     match and will reproduce the same `invalid-publisher` error.
5. Click **Add**. No token/secret is generated or copied — trust takes effect via OIDC token
   matching on the next run; there is no separate "activation delay" step to wait out.

**Permission level required**: PyPI's docs describe two project-collaborator roles — a
Maintainer can upload releases, an Owner can manage the project and its collaborators. The docs
do not explicitly say Publishing-settings edits are Owner-only, but "manage the project" is the
closest fit and it is the safe assumption. If the Publishing page appears read-only/inaccessible
for an account that does show up under "Your projects," that is itself the signal the account
holds Maintainer, not Owner, on that project.

### If the account lacks any role on the existing project (fallback ladder)

The task's caveat is correct: `author_email` in the uploaded 0.1 package metadata is
self-declared build-time metadata, not proof of TestPyPI account control. The **authoritative**
signal is the **Maintainers list on the live project page**,
`https://test.pypi.org/project/model-checker/`, which shows the actual TestPyPI usernames
holding a role — compare that against the user's own TestPyPI username first, before assuming
anything is blocked.

If it turns out another account (plausibly the co-author, Miguel Buitrago, per the recorded
`author_email`) holds the only role:

1. **Ask the existing owner to add the user as a collaborator.** Fastest, zero workflow risk:
   the existing owner visits the project's Collaborators page and grants Owner (or at minimum a
   role permitting Publishing edits) to the user's TestPyPI account, or simply registers the
   trusted publisher themselves using the exact field values in the procedure above. No
   `release.yml` change needed either way.
2. **Request ownership transfer via PyPI/TestPyPI support** if the existing owner is
   unreachable. File at `https://github.com/pypi/support` (the shared support tracker Warehouse
   uses for both pypi.org and test.pypi.org). Two caveats to flag to the user rather than assume:
   - PEP 541 (the abandonment/name-retention policy requiring proof of failed contact attempts,
     a working fork, etc.) is written for production PyPI; whether TestPyPI support applies the
     same strict bar, a lighter one, or handles it case-by-case is **not documented** and should
     be asked directly in the support issue, not assumed.
   - Separately, community reports (`pypi/support` issues, Python Discourse) describe TestPyPI's
     database as periodically pruned, with stale/abandoned accounts sometimes removed —
     unpredictable and not self-service, but worth mentioning as context for why support might
     resolve this faster than the equivalent request would on production PyPI.
3. **Publish the TestPyPI rehearsal under a different, currently-unclaimed project name**, using
   the ordinary "pending publisher" flow (Account Settings → Publishing → "Add a pending
   publisher"), which *does* apply here since a brand-new name has never been used. This
   sidesteps the ownership dispute entirely but has a real implementation cost worth surfacing
   now rather than discovering later: `publish-testpypi` and `publish-pypi` currently consume the
   **same** `dist` artifact (built once in the `build` job, downloaded by both — release.yml:129-134,
   150-154, 171-175), and the package name is baked into that artifact's wheel/sdist metadata at
   build time. Publishing that artifact under a different name on TestPyPI is not a
   `repository-url`-only change; it would require either a second, TestPyPI-only build with an
   overridden project name, or accepting a rehearsal that verifies differently-named bytes than
   what actually reaches production PyPI — weakening the rehearsal's value. Treat this as a
   last-resort option requiring explicit user sign-off, not something to implement unprompted.

Whichever path is chosen, **all of it is user-only web-UI/account work** (options 1 and 2 involve
no workflow file change at all; option 3 would need a `release.yml`/build change but only if the
user explicitly accepts that tradeoff). The agent must not attempt to log in, register, or
otherwise touch test.pypi.org itself — this is squarely the user gate the task calls for.

## (B) Minting and decoding the OIDC token for a diagnostic print

### Audience value — confirmed to differ between PyPI and TestPyPI

Direct fetch results:
- `https://pypi.org/_/oidc/audience` → `{"audience":"pypi"}`
- `https://test.pypi.org/_/oidc/audience` → `{"audience":"testpypi"}`

These are **different strings**, not a single "pypi" constant reused everywhere. Confirmed
against the actual mechanism `pypa/gh-action-pypi-publish` itself uses: its `oidc-exchange.py`
(unstable/v1 branch) derives the audience at runtime by `GET`-ing
`https://{repository_domain}/_/oidc/audience` — where `repository_domain` comes from whatever
`repository-url` the job configured — rather than hardcoding either string. For the
`publish-testpypi` job, `repository-url: https://test.pypi.org/legacy/` (release.yml:159) means
the correct audience is `testpypi`.

**Implication for the diagnostic step**: either (i) hardcode `audience=testpypi` — simple and
correct today, but silently stale if `repository-url` ever changes — or (ii) fetch
`https://test.pypi.org/_/oidc/audience` first and use its `.audience` value, exactly mirroring
upstream's own approach. (ii) is one extra `curl` call and is the more idiomatic, drift-proof
choice; either is acceptable for a diagnostic-only step.

### Mechanism: plain `curl` + `jq`, not `actions/github-script`

Recommend a plain bash step using `curl`/`jq`, for three reasons:
1. **Consistency**: every existing step in `release.yml` is plain bash (`shell: bash` /
   default `run:` blocks) — no step currently uses `actions/github-script`. Introducing it here
   for one diagnostic line adds a new action pin and a Node-in-YAML script for no functional gain.
2. **This is the pattern GitHub itself publishes as the reference implementation**:
   `github/actions-oidc-debugger` (an official `github` org repo) uses exactly this recipe —
   `curl` against `$ACTIONS_ID_TOKEN_REQUEST_URL&audience=...` with
   `Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN`, extract `.value` with `jq`, split the
   JWT on `.`, base64url-decode the middle (payload) segment, and re-pipe through `jq` for
   readable output. `actions/github-script`'s `core.getIDToken(audience)` is a real, documented
   alternative but is aimed at consuming the token programmatically for an API call, not at a
   one-off diagnostic print.
3. **Fewer moving parts under a `continue-on-error` diagnostic step**: `curl`/`jq` are already
   present on `ubuntu-latest` runners; failure handling (`|| true`, or step-level
   `continue-on-error: true`) is simpler to reason about than a script step's internal
   try/catch.

Concrete recipe:
```bash
TOKEN_JSON=$(curl -sS -H "Authorization: bearer ${ACTIONS_ID_TOKEN_REQUEST_TOKEN}" \
  "${ACTIONS_ID_TOKEN_REQUEST_URL}&audience=testpypi")
JWT=$(echo "$TOKEN_JSON" | jq -r '.value')
PAYLOAD=$(echo "$JWT" | cut -d '.' -f2)
echo "$PAYLOAD" | base64 -d 2>/dev/null | jq '{sub, repository, workflow_ref, environment}'
```
(Padding note: raw JWT base64url payloads are sometimes missing `=` padding; `base64 -d` on GNU
coreutils tolerates this in practice, but a hardened version should pad to a multiple of 4 before
decoding, as the upstream `extract_claims` implementation and the `actions-oidc-debugger` recipe
both do.)

### Hard constraints — how each is satisfied

- **Never print the raw token**: `$ACTIONS_ID_TOKEN_REQUEST_TOKEN` and `$JWT` are only ever
  assigned to shell variables and piped through `base64 -d | jq`, filtered to the four named
  fields. No `echo "$JWT"`, no writing either value to `$GITHUB_OUTPUT`, `$GITHUB_ENV`, an
  artifact, or a log line anywhere in the step.
- **Never write it to a step output/artifact/env file/log**: the whitelisted `jq` filter
  (`{sub, repository, workflow_ref, environment}`) is the *only* thing that reaches stdout (and
  therefore the job log); nothing is set via `>> $GITHUB_OUTPUT` / `>> $GITHUB_ENV` / uploaded as
  an artifact.
- **Never fail the job**: apply `continue-on-error: true` at the **step** level on this new
  diagnostic step specifically (a distinct, per-step YAML attribute from the job-level
  `continue-on-error: true` already on line 147, which covers the whole `publish-testpypi` job
  and is scoped separately from any future removal of that job-level flag in the dependent
  hardening task). Step-level `continue-on-error: true` also renders distinctly in the Actions UI
  (a yellow triangle rather than a red X) if the mint/decode fails, which is itself useful signal
  distinct from the actual publish step's outcome.
- **GitHub's secret masking does not cover this token**: `ACTIONS_ID_TOKEN_REQUEST_TOKEN` and the
  minted JWT are both generated at runtime and are not registered `secrets.*` values, so GitHub's
  automatic log-masking does **not** apply to them — printing either verbatim would leak a
  short-lived-but-real bearer credential into a log that is not redacted. This is the concrete
  reason the implementation must never `echo` the full token/JWT and must route only the
  post-decode, whitelisted JSON to stdout. (If a future revision ever needs to handle a value
  that must stay hidden, `::add-mask::<value>` is the explicit escape hatch, but it is not needed
  here since the four printed claims — `sub`, `repository`, `workflow_ref`, `environment` — are
  not secret.)

## (C) Existing upstream diagnostic idiom — yes, and it already fires today

This is the most load-bearing finding for scoping the implementation correctly.

`pypa/gh-action-pypi-publish`'s own `oidc-exchange.py` (source read directly, `unstable/v1`
branch) **already implements almost exactly this diagnostic pattern**, and it already runs
automatically on every `invalid-publisher` failure. Its `extract_claims` function splits the
JWT, base64-decodes the payload, and renders `sub`, `repository`, `repository_owner`,
`repository_owner_id`, `workflow_ref`, `job_workflow_ref`, `ref`, and `environment`, prefaced
with: *"The claims rendered below are for debugging purposes only. You should not use them to
configure a trusted publisher unless they already match your expectations."* (confirmed via the
action's GitHub issue #217 discussion, which quotes this exact message). This claim set and
framing is precisely what produced the "FRESH EVIDENCE" block quoted verbatim in the task
description — i.e., **that block already came from this exact upstream mechanism**, not from any
bespoke tooling.

`docs.pypi.org/trusted-publishers/troubleshooting/` (fetched directly) complements this with a
config-comparison checklist rather than an in-workflow recipe: *"For GitHub, check that the
`repository_owner`, `repository` and workflow filename values are the same on both sides"* and,
for environment mismatches, *"check if the workflow is using the same environment as configured
when the publisher was configured on PyPI."* It does not itself prescribe a minting/decoding
recipe — that idiom lives in the action's own source and, independently, in GitHub's own
reference tool `github/actions-oidc-debugger` (curl + jq, described in section B), which
corroborates the same recipe from a completely separate source.

**Practical implications for scope**:

1. The claims data this task wants surfaced is **not new information** — it already appears in
   the CI logs today, inside the failed `Publish to TestPyPI` step's own output, exactly because
   `pypa/gh-action-pypi-publish` prints it on every `invalid-publisher` rejection. What is
   currently missing is not the data but the *one-glance-ability*: a user has to open the failed
   job, expand the upload step's log, and find the block, rather than seeing a clearly labeled,
   dedicated step summary. A separate preceding diagnostic step (as the task's component 2
   specifies) still adds real value for that reason, and additionally would surface claims even
   in a hypothetical future where the upload step is gated behind a precondition and might not
   run at all.
2. Because upstream already defines the "right" vocabulary, the new step should **reuse it
   rather than invent a parallel one** — same field names (`sub`, `repository`, `workflow_ref`,
   `environment` at minimum, optionally `job_workflow_ref`/`repository_owner`/`ref` matching
   upstream's fuller set), and ideally the same "for debugging purposes only, don't use to
   configure a publisher unless already matching your expectations" disclaimer, so the new step's
   output reads as consistent with what the action itself already prints on failure rather than
   as a second, differently-shaped diagnostic surface.
3. No conflicting or competing upstream recommendation was found — `pypa/gh-action-pypi-publish`,
   `docs.pypi.org`, and GitHub's own `actions-oidc-debugger` all converge on the same claim set
   and the same curl+jq/JWT-payload-decode mechanism. There is no basis here for inventing a
   different pattern.

## Sources

- [Adding a Trusted Publisher to an Existing PyPI Project](https://docs.pypi.org/trusted-publishers/adding-a-publisher/)
- [Trusted Publishers Troubleshooting](https://docs.pypi.org/trusted-publishers/troubleshooting/)
- [Trusted Publishers Security Model](https://docs.pypi.org/trusted-publishers/security-model/)
- [pypa/gh-action-pypi-publish issue #217 — invalid-publisher part 2](https://github.com/pypa/gh-action-pypi-publish/issues/217)
- [pypa/gh-action-pypi-publish `oidc-exchange.py` (unstable/v1)](https://github.com/pypa/gh-action-pypi-publish/blob/unstable/v1/oidc-exchange.py)
- [github/actions-oidc-debugger README](https://github.com/github/actions-oidc-debugger/blob/main/README.md)
- [GitHub Docs — OpenID Connect reference](https://docs.github.com/en/actions/reference/security/oidc)
- `https://pypi.org/_/oidc/audience` and `https://test.pypi.org/_/oidc/audience` (fetched directly, confirmed `pypi` vs `testpypi`)
- [pypi/support (shared PyPI + TestPyPI support tracker)](https://github.com/pypi/support)
- [PEP 541 – Package Index Name Retention](https://peps.python.org/pep-0541/)
- Repo files read directly: `.github/workflows/release.yml`, `.github/RELEASE_SETUP.md`, `specs/TODO.md` (task 161 and dependent task 158 entries)
