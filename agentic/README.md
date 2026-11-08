# Proof-agent benchmark CLI

## Proof automation

The benchmark harness in `agentic/prove.sh` runs the Python Codex workflow and checks
solutions with `lake comparator --config=...`.

Workspaces preserve module paths and copy immediate files from the selected task and its
ancestors under `CPSLib`, together with Core and Tactic. Only the selected task's `Proof.lean`
is withheld; parent proofs remain reusable. Subdirectories are not copied. A fresh
`Solution.lean` is created beside the selected Challenge, and the workspace config points to it.
Judging copies only that solution into a separate trusted snapshot.

The harness copies the [CPSLib prover skill](agentic/skills/cpslib-prover/SKILL.md)
into each agent workspace. See [the harness README](agentic/README.md) for details.

Run the complete workflow from the repository root (it creates the agent workspace under ./benchmark-results):

```sh
agentic/prove.sh run CPSLib/Examples/BouncingBall codex --model gpt-6.1-sol
```

The stages can also be run separately:

```sh
agentic/prove.sh prepare CPSLib/Examples/BouncingBall ./BouncingBall-sandbox
agentic/prove.sh agent codex ./BouncingBall-sandbox
agentic/prove.sh judge CPSLib/Examples/BouncingBall ./BouncingBall-sandbox/CPSLib/Examples/BouncingBall/Solution.lean
```

Run `agentic/prove.sh help` for more information.

## Installation

Run the following project commands from the repository root. The harness uses
Python 3.11+, Git, GNU `timeout`, and the Lean toolchain pinned in `lean-toolchain`.
Judging also requires a Linux environment that supports the native Comparator
sandbox, including Bubblewrap (`bwrap`).

On Debian/Ubuntu, install the system prerequisites:

```sh
sudo apt update
sudo apt install curl git coreutils bubblewrap
```

Install [uv](https://docs.astral.sh/uv/getting-started/installation/), then reopen
your terminal or load its shell environment:

```sh
curl -LsSf https://astral.sh/uv/install.sh | sh
. "$HOME/.local/bin/env"
uv --version
```

Install Python and the locked project dependencies. This creates `agentic/.venv`;
there is no need to activate it when using `uv run` or `prove.sh`.

```sh
uv python install 3.11
uv sync --project agentic --locked --python 3.11
```

If Lean is not installed, install its
[elan toolchain manager](https://leanprover-community.github.io/get_started.html):

```sh
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh
. "$HOME/.elan/env"
```

Prepare the Lean dependencies from the repository root. Elan selects the pinned
Lean version automatically; do not replace it with a different global version.

```sh
lake exe cache get
lake build
lake comparator --help
uv run --project agentic --locked cpslib-prove help
```

The harness uses the Codex runtime bundled with its Python SDK. To authenticate
with a ChatGPT account, an existing file-based Codex login can be reused. If you
need the standalone CLI for login, install Node.js/npm through your package
manager, then follow the [official Codex authentication documentation](https://developers.openai.com/codex/auth):

```sh
npm install -g @openai/codex
codex -c 'cli_auth_credentials_store="file"' login
codex -c 'cli_auth_credentials_store="file"' login status
```

File storage is specified because the harness links `auth.json` from
`$CODEX_HOME` (default `~/.codex`) into its private runtime home. A login stored
only in the OS keyring is not copied. Authentication is needed for `agent` and
`run`; `prepare` and `judge` do not call Codex.

## Usage

`agentic/prove.sh` is a thin wrapper for `uv run --project agentic --locked
cpslib-prove`. Both entry points run the same Codex SDK implementation.

```sh
agentic/prove.sh prepare CPSLib/Examples/FM09/Extra /tmp/fm09-extra
agentic/prove.sh agent codex /tmp/fm09-extra --timeout 600
agentic/prove.sh judge CPSLib/Examples/FM09/Extra /tmp/fm09-extra/CPSLib/Examples/FM09/Extra/Solution.lean /tmp/fm09-judge
agentic/prove.sh run CPSLib/Examples/FM09/Extra codex --model gpt-6.1-sol
```

`prepare` creates a new workspace, builds the qualified Challenge module, and
initializes a fresh Git repository. It preserves original module paths and copies
immediate files from the selected task and each ancestor through `CPSLib`, plus
Core and Tactic recursively. Sibling and child directories are omitted. Only the
selected task's `Proof.lean` is excluded; parent proofs are reusable library
material. Existing `Solution.lean` files are omitted and a fresh solution is seeded
from the selected Challenge. Symlinked support sources are rejected.

The generated task config keeps its qualified `challenge_module` and changes
`solution_module` to the sibling Solution module. Repository configs are unchanged.
No `trusted_dependencies` list, Comparator checkout, executable path variables,
Landrun, or systemd wrapper is needed. The native command uses its own sandbox.

`agent` runs Codex in a prepared workspace and saves JSON SDK notifications and
worker diagnostics. `judge` creates a fresh trusted snapshot and transfers only
the submitted Lean file before running `lake comparator --config=TASK/config.json`.
`run` prepares separate trusted and agent projects, runs Codex, then transfers
only the solution to the trusted project for judging. Agent edits to models,
configs, instructions, and build artifacts do not transfer to the judge.

Output directories must be new. Relative paths are resolved from the caller's
working directory. Defaults are `./NAME-sandbox`, `./NAME-judge`, and
`benchmark-results/TIMESTAMP-NAME-codex`. Metadata records the source fingerprint,
toolchain, and Git revision/dirty status. A run records both exit codes in
`result.txt`; a failing Comparator takes precedence over the agent exit code.

| Commands | Option | Meaning |
| --- | --- | --- |
| `agent`, `run` | `--model MODEL` | Default `gpt-6.1-sol`. |
| `agent`, `run` | `--timeout SECONDS` | Positive limit; default 600. |
| `run` | `--output DIRECTORY` | New run directory. |
| `run` | `--skip-judge` | Run the agent without judging. |

Fire accepts underscores and hyphens. Place boolean flags last or use an explicit
value such as `--skip-judge=True`. Use `agentic/prove.sh COMMAND --help` for details.

Codex uses approval-disabled ephemeral SDK threads with workspace writes and
read access to its runtime, Lean toolchain, trusted dependency cache, and optional
Lean skills. Network access and web research are enabled. A private temporary
`CODEX_HOME` avoids loading user rules/history and reuses file-based authentication
when available. GNU `timeout` terminates the worker and its process group after
the limit, with a 30-second grace period. `CODEX_BIN` optionally overrides the SDK
runtime; `ELAN_BIN` overrides the toolchain resolver. Source Git history is never
copied into the workspace.

Development checks:

```sh
agentic/.venv/bin/python -m unittest discover -s agentic/tests
agentic/.venv/bin/ruff check agentic
agentic/.venv/bin/pyright --project .
```
