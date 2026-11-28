# Independent verification of release v0.0.1

**Release:** `v0.0.1` ("Pre-Release for External Verification"), tag `v0.0.1`,
commit `99c5ef7aaa33b92b01534b307859b4867468cc47`
("Add Python TF-IDF statement clustering script and tests", 2026-11-28).
**Verified:** 2026-11-28, independently, on a machine that had never built this
project before. **Scope:** (1) independent verification with `con-leche`,
`con-ron`, `Nanoda`, `lean4lean`, `comparator`, `con-leche --compare`;
(2) tips on integrating with
[NUS-Math-Formalization/coxeter](https://github.com/NUS-Math-Formalization/coxeter)
and [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4).
No Lean code was changed. This document is the complete record; it is the only
file in this PR.

## Verdict summary

| Check | Result |
|---|---|
| Independent clean build from the tag | **PASS** — exit 0, 3,662 jobs, exactly as claimed |
| `sorry` / `admit` / extra `axiom` audit | **PASS** — zero hits in all three Lean directories |
| `#print axioms` on the 19 registry symbols | **PASS** — only `propext`, `Classical.choice`, `Quot.sound` |
| `lake check` (leanchecker, sandboxed replay) | **NO VERDICT** — three attempts, all blocked by this VM's limits (see §4) |
| `lake check --paranoid` (nanoda, lean4lean, con-leche, con-ron) | **NOT RUN** — needs the full-closure export `lake check` could not produce |
| Direct `leanchecker` sweep (replacement evidence) | **PASS** — 26/26 submodules accepted, exit 0 |
| Full axiom audit of all 2,413 declarations (replacement evidence) | **PASS** — only the three standard axioms, no `sorryAx` |
| `comparator` / `con-leche --compare` | **BLOCKED** — no challenge exists; building one needs a definitions/theorems split (§5) |
| Integration tips | Done — §6 |

The two headline claims that could be checked here hold: the build reproduces
exactly (3,662 jobs) and the code is sorry-free with standard axioms only.
The two checks that would give the strongest independent assurance —
`lake check` / `--paranoid` and the comparator — could not be completed on this
machine, for the environment reasons documented below. They need a bigger
machine (see §7), not different code.

## 1. Environment

Verification ran on a Linux VM with 4 CPUs and 7.7 GiB RAM (the checking
process's cgroup cap was ~6.0 GiB), 147 GiB free disk, `/tmp` a 512 MiB tmpfs.
None of `elan` / `lake` / `lean` was installed; everything below was installed
fresh for this verification.

| Tool | Version |
|---|---|
| elan | `4.4.0 (3cc76985a 2026-11-18)`, installed from `elan-init.sh` (`https://elan.lean-lang.org` returned HTTP 404 on this VM, so the installer was fetched from `https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh`; `sh /tmp/elan-init.sh -y --default-toolchain none`, exit 0) |
| Lean | `4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release` (the version pinned by `lean/lean-toolchain`: `leanprover/lean4:v4.35.0`) |
| Lake | `5.0.0-src+eb6cafb (Lean version 4.35.0)` |
| Mathlib | rev `56a005855ea1…` (`v4.35.0`), 9,031 cache files from `cache.mathlib.org` |

Checkout verified: fresh `git clone`, `git checkout v0.0.1`, HEAD
`99c5ef7aaa33b92b01534b307859b4867468cc47`; `v0.0.1` is an annotated tag
(tag object `606eae3…`, tagger J Kyle Armstrong, "v0.0.1 pre-release for
external verification"); `git describe --tags HEAD` = `v0.0.1`; worktree clean
after the build (only ignored `.lake/` created).

## 2. Independent build — PASS

From the fresh checkout, in `lean/`:

- `lake exe cache get` — exit 0, wall 872 s (14 m 32 s). Built the cache
  executable (43/43 jobs), fetched Mathlib rev `56a005855ea1…`, downloaded
  9031/9031 files and decompressed all. (Download was slow, ~2–95 KB/s per file.)
- `lake build -j2` — **rejected**: `error: unknown short option '-j'` (exit 1,
  1 s). Lake 5.0.0 has no `-j`/`--jobs` flag. The repo's own CI runs plain
  `lake build`, so that is what was run, under `taskset -c 0,1` to cap CPU.
  (Caveat: `taskset` capped CPU to 2 cores but Lake still scheduled up to 4
  concurrent `lean` processes; peak per-process RSS ~3.9 GiB, mostly shared
  mmap'd oleans; no OOM — `/proc/vmstat oom_kill 0`, swap peaked ~386 MB.)
- `taskset -c 0,1 lake build` — **exit 0, wall 1,103 s (18 m 23 s)**. Final
  line: `Build completed successfully (3662 jobs).` All 26 module oleans plus
  `MixedSignCoxeter.olean` exist under `.lake/build/lib/lean/`.

**Job count: 3,662 — exactly matches the release claim.** Method: Lake's own
final summary line, corroborated by the per-target lines `[3635/3662]` …
`[3661/3662]` (jobs 1–3634 are dependency/Mathlib jobs, up-to-date from
cache). Slowest modules: TwoDefectCycle 611 s, ReflectionSystem 352 s,
EvenCycleSingleDefect 300 s, AlternatingSquare 272 s.

**0 errors** (no line starting with `error:` in the 110,547-line build log).
**384 warnings**, including 269 unused-simp-arg linter warnings, 42
deprecation warnings, and 39 "consider adding `module`" import warnings. (One
log line mentions "The `ring` tactic failed…" — it is inside an `info: Try
this:` hint at `OddCycleSingleDefect.lean:298`, not a build error.)

Scope note: `lean/MathlibDraft/` is a declared `[[lean_lib]]` but not a
default target (`defaultTargets = ["MixedSignCoxeter"]`), so `lake build`
does not build it (no MathlibDraft oleans were produced). `lean/mathlib_pr/`
is not a lake target at all (0 mentions in `lakefile.toml`). The release's
"26 sorry-free modules" claim refers to `lean/MixedSignCoxeter/` only.

## 3. Sorry / axiom audit — PASS

**Grep audit — clean.** `grep -rn -E '\bsorry\b|\badmit\b'` and
`grep -rn -E '^\s*axiom\s'` over `lean/MixedSignCoxeter/` (26 modules, 14,751
lines), `lean/MathlibDraft/` (11 modules), and `lean/mathlib_pr/` (1 module):
**zero hits in all three directories**, including a case-insensitive `sorry`
substring sweep (no hits even in comments). Module census: 214 `theorem` +
175 `lemma` declarations across the 26 modules.

**`#print axioms` on the registry — standard axioms only.** A scratch file
imports `MixedSignCoxeter` and runs `#print axioms` on all 19 symbols of the
project's statement registry (`data/theorems.yml`, 18 entries / 19 Lean
symbols); `lake env lean` on it exits 0 in 10 s. **Every one of the 19
depends only on `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.**

| Symbol | File:line |
|---|---|
| `ReflectionSystem.howlett_principalElement_eq_neg_inv_mul_transpose` | Howlett.lean:219 |
| `ReflectionSystem.bipartite_conjugation_theorem` | Bipartite.lean:65 |
| `MixedSignCoxeter.theorem_1_6_tildeAminus_iso_D` (noncomputable def) | TildeAminusEvenIso.lean:369 |
| `ReflectionSystem.bipartite_principalElements_conjugate` | Bipartite.lean:208 |
| `MixedSignCoxeter.tildeAminus2_fails_deletion` | CyclesAndDeletion.lean:120 |
| `MixedSignCoxeter.w_A3_ppm_add_one_cube` | SpectralRadius.lean:72 |
| `MixedSignCoxeter.theorem_3_9_classical_iff_deletion` | ClassicalCoxeterDeletion.lean:407 |
| `MixedSignCoxeter.RootPositivity.prop_3_10` | RootPositivity.lean:680 |
| `MixedSignCoxeter.RootPositivity.classical_graph_isClassicalCoxeter` | RootPositivity.lean:912 |
| `MixedSignCoxeter.theorem_3_34_bipartite_exceeds_linear` | SpectralRadius.lean:211 |
| `MixedSignCoxeter.alternatingSquare_principal_not_conjugate` | AlternatingSquare.lean:101 |
| `MixedSignCoxeter.oddCycleSinglePlus_minimal_poly` | OddCycleSingleDefect.lean:818 |
| `MixedSignCoxeter.evenCycleSinglePlus_has_eigenvalue_lt_neg_one` | EvenCycleSingleDefect.lean:1296 |
| `ReflectionSystem.principalElement_bipartiteSignFlip` | BipartiteDuality.lean:141 |
| `MixedSignCoxeter.evenCycleAdjTwoDefect_complex_eigenvalue_norm_gt_one` | TwoDefectCycle.lean:2062 |
| `MixedSignCoxeter.theorem_1_6_tildeAminus_odd_infinite` | TildeAminusEvenIso.lean:632 |
| `ReflectionSystem.finite_connected_isDefinite` | FiniteReduction.lean:193 |
| `MixedSignCoxeter.appendixD_relators_hold` | TildeAminusEvenIso.lean:528 |
| `ReflectionSystem.k_component_mulEquiv` (noncomputable def) | ComponentsAndTrees.lean:379 |

**Clarification on the "107" figure.** `data/theorems.yml` has 18 entries (19
Lean symbols), not 107. The "107" is 107 *dissertation statements* used by
`scripts/statement_clusters.py` (TF-IDF clustering; README.md:37), not 107
Lean theorems. The axiom audit therefore covered the complete registry (all
19 symbols) rather than a sample. The 26 modules contain 389 proof
declarations total (214 theorems + 175 lemmas); only the 19 registry symbols
were individually `#print axioms`-checked — the clean build plus the zero-sorry
grep is what covers the other 370 for sorry-freedom. (The full-declaration
axiom audit in §4.3 covers all of them transitively.)

## 4. Kernel verification — `lake check` has NO VERDICT here

### 4.1 `lake check` — three attempts, all blocked by the environment

**Attempt 0 — sandboxed (as intended).** `lake check`, 2026-11-28
14:10:24–14:10:25 UTC (~1 s), **exit 1**. Verbatim log: `Resolving
dependencies` / `bwrap: Can't mount proc on /newroot/proc: Operation not
permitted` / `error: Child exited with 1`. The bubblewrap sandbox cannot mount
`/proc` in this environment (user namespaces are enabled —
`unprivileged_userns_clone=1` — the proc mount itself is denied). No kernel
verdict. Fell back to `--inadvisably-no-sandbox` as instructed.

**Attempt 1 — `lake check --inadvisably-no-sandbox`, default `TMPDIR=/tmp`.**
14:11:05 → killed 16:06:28 UTC (115 min 23 s), exit 143 (SIGTERM, killed by
the verifier). Two compounding failures: (a) `leanexport` writes its NDJSON
export to `/tmp`, a **512 MiB tmpfs**, but the full-closure export is ~2.8 GiB
— the file filled `/tmp` exactly and was **truncated at 532,692,992 bytes**
(9,824,707 lines + partial line, tail cut mid-JSON; only 5
`MixedSignCoxeter` mentions — project modules export last, so none of the
project's own declarations were in it); (b) the process then **wedged in a
pipe-relay deadlock**: inner lake PID frozen (utime/stime unchanged across
repeated observations) with a thread blocked in `anon_pipe_write` (full stdout
pipe), outer lake with a reader thread blocked in `anon_pipe_read` (empty
pipe). No log output beyond `Resolving dependencies` in 115 min. Memory was
tight but was **not** the wedge cause (RSS stable ~1.64 GiB, no OOM kills).

**Attempt 2 — same, with `TMPDIR` on the big disk (144 GiB free).**
16:06:44 → killed by a **runtime/VM restart** ~17:06:02 UTC (~59 min in).
Healthy while it ran (export grew steadily to 2,679,451,648 bytes; inner lake
CPU 16–35%, RSS ~4.6–5.1 GiB). Export left truncated mid-record. Log lost
with the `/tmp` wipe. No verdict.

**Attempt 3 — same, `TMPDIR` on the big disk, logs in the workspace.**
17:06:54 → killed by the verifier 19:01:52 UTC (114 min 58 s, exit 143).
Export grew to 2,809,303,040 bytes by ~68 min (18:11 UTC), then **no growth
for 50 min** while the exporter ground on page-cache thrash (user CPU
advancing only ~16 ticks/min, `read_bytes` +~50 MB/s to 343 GB cumulative,
1,043,217 major page faults, RSS ~4.7 GiB). The export *was* in its final
phase — full `thm` records for project theorems
(`theorem_3_27_classification`, `w_altSq_bp_eq`, `trace_w_altSq_bp`,
`alternatingSquare_principal_not_conjugate`) are present, 298,863 thm +
124,555 def records, 49,536,458 lines — but the file's last bytes are a
partial record (`{"thm":{"all":[251`), so it is incomplete on disk. Killed:
no credible ETA for the export to finish, let alone the replay. The partial
export is preserved at `~/workspace/msc-verify-tmp/tmp.XXY14cgZ`
(2,809,303,040 bytes) for the record.

**`lake check --paranoid` — NOT RUN.** It requires the full-closure export,
which could not be produced on this VM (see above). Running the paranoid
checkers on the incomplete partial export would be meaningless, so it was not
attempted. Per-kernel paranoid results (nanoda, lean4lean, con-leche, con-ron,
`leanchecker-paranoid`) therefore **do not exist** for this release from this
verification.

### 4.2 Replacement evidence 1 — direct `leanchecker` sweep: 26/26 ACCEPTED

`lake check` replays a serialized export through a fresh kernel without
trusting oleans; that replay could not run here. What could run is the same
stripped official kernel (`leanchecker`) invoked directly on the existing
oleans, one module at a time — reported as replacement evidence, not as
`lake check`:

- `lake env leanchecker <module>` for each of the 26 submodules, sweep
  19:11:25 → 19:17:02 UTC (~5.5 min): **26/26 exit 0** (8–38 s each:
  AlternatingSquare 38 s, SpectralRadius 19 s, TwoDefectCycle 18 s,
  SpectralClassification 14 s, rest 8–13 s). `leanchecker` is silent on
  accept (no per-declaration output).
- The root module `MixedSignCoxeter` exits **137 (OOM-killed)** after 37 s —
  it imports all 26 submodules, and loading the full closure exceeds the
  ~6.0 GiB cgroup cap (same signature as the full 27-module invocation, exit
  137 at 2 min 25 s). The root contains **zero declarations of its own** (26
  import lines only, verified by grep), so the OOM loses no declaration
  coverage: every project declaration lives in a submodule, and all 26
  submodules were accepted.
- Spot re-run for reproducibility: `leanchecker
  MixedSignCoxeter.TwoDefectCycle` again exit 0 (19:25:21 → 19:25:46 UTC,
  25 s). Validation that exit 0 is meaningful: `leanchecker
  NonExistent.Module` exits 1 (`Could not find any oleans for:
  NonExistent.Module`); no-arg `leanchecker` exits 1.

Caveat: this sweep checks each module's declarations against its (trusted,
olean-loaded) dependency environment; it is **not** the export-replay path
`lake check` uses. The two agree in what they verify per-declaration, but
they are not the same procedure.

### 4.3 Replacement evidence 2 — full axiom audit: 2,413 declarations, standard axioms only

Per-module audit files import the module and, in a `run_cmd`, enumerate every
declaration defined in that module (`env.getModuleIdxFor? ==
env.getModuleIdx? <module>`) and run `Lean.collectAxioms` on each; the run
fails if any declaration depends on an axiom outside `{propext,
Classical.choice, Quot.sound, Lean.ofReduceBool}`. Sweep 19:21:12 → 19:24:27
UTC (~3 min 15 s): **26/26 modules PASS, 2,413 declarations checked in
total. Every module's distinct-axiom set is exactly `{propext,
Classical.choice, Quot.sound}`** — no `sorryAx`, no `Lean.ofReduceBool`,
nothing else, in any module. Per-module counts include EvenCycleSingleDefect
340, TwoDefectCycle 354, OddCycleSingleDefect 229, TildeAminusEvenIso 146,
SpectralClassification 143, RootPositivity 137. `collectAxioms` is transitive,
so this covers `sorryAx` anywhere in any dependency tree. Source-level
corroboration: grep finds 0 `sorry`, 0 `sorryAx`, 0 `axiom` declarations in
all project source; the single `admit` hit is the English word "admits" in a
comment (`ClassicalDeletion.lean:65`).

### 4.4 Checker inventory (Lean 4.35.0 toolchain)

Binaries live in the toolchain
(`~/.elan/toolchains/leanprover--lean4---v4.35.0/bin/`); there is no
`.lake/build/bin/` in the project. Sizes/dates: `con-leche` 17,613,744 B,
`con-ron` 2,945,520 B, `lean4lean` 36,897,680 B, `leanchecker` 59,656 B,
`leanchecker-paranoid` 8,858,080 B, `nanoda_bin` 1,339,280 B (all Oct 12).
`nanoda_bin` is **0.4.19** (from `--help`; `--version` treats the arg as a
config path; Rust, rustc 1.94.0). `con-leche`/`con-ron` accept no `--version`
(usage error); no version string in `--help` or `strings` (only embedded
prelude meta: exporter `con-leche-prelude` v1, format 3.1.0, Lean githash
`470d5ce…`, version `4.35.0-rc3`). `leanchecker`/`lean4lean`/
`leanchecker-paranoid` are part of Lean 4.35.0 (toolchain commit `eb6cafb`).
`con-ron --help` footer: "this build's global allocator: mimalloc". `bwrap`
is 0.9.0. `lake check --help` exit codes: 0 = all selected checkers accept +
only permitted axioms; 1 = checker rejects / unpermitted axiom / build fails;
2 = cannot start.

**`--compare` does NOT exist in the bundled binaries.** Full `--help` text
captured for both: `con-leche` flags are `--verified`, `--trusted`,
`--jobs=<n>`, `--no-mark-persistent`, `--progress[=<stride>]`, `--help`;
`con-ron` adds `--pins FILE` / `--no-pins`. `con-ron` states: "Any other
option is a usage error: the run reports it, prints this text and exits 3
without reading its input." No `con-leche --compare` was run (no challenge
exists yet) — the flag simply is not present to run.

## 5. Comparator / `--compare` — BLOCKED on a definitions/theorems split

### 5.1 What the challenge would be

A repo-wide grep for `comparator`, `--compare`, `challenge`, `con-leche`,
`con-ron`, `leanchecker`, `paranoid` returns nothing: **no challenge export
exists in the repo**. The challenge set was determined from the repo's own
registries:

- `data/theorems.yml` has only 18 entries with English prose statements — not
  a challenge.
- The real source is `docs/assets/mixed_sign_coxeter_statements_lean.csv`
  (107 rows). Auditing every symbol against the actual `.lean` sources
  (declaration-name search + namespace/section scope tracking — the CSV's line
  numbers are stale in places, e.g. `W_group_preserves_B` is claimed in
  `FiniteReduction.lean` but lives at `ReflectionSystem.lean:310`):
  - **Challenge set = 52 unique theorem/lemma symbols**: 50 with
    `lean_status` "Verified" + 2 counterexample theorems answering open
    questions 2.59/3.35
    (`MixedSignCoxeter.alternatingSquare_principal_not_conjugate`,
    `..._bipartite_not_min`). Fully-qualified names computed and spot-checked.
  - **Excluded with reason**: 3 "Verified" symbols are `noncomputable def`s,
    not Props (`ReflectionSystem.k_component_mulEquiv`,
    `MixedSignCoxeter.freeCoxeterQuotient`,
    `MixedSignCoxeter.theorem_1_6_tildeAminus_iso_D`) — candidates for
    `definition_names`, not `theorem_names`; plus 59 auxiliary API lemmas
    behind "Formalized (definition/remark/example)" rows (proved but not
    dissertation statements).
  - All 52 statements were extracted verbatim from v0.0.1 sources (52/52, 0
    failures; 42 `by` proofs, 10 term proofs; library confirmed sorry-free).

### 5.2 The blocker

A Challenge module must import the definitions used in the statements
**without** importing the challenged theorems (redeclaring an imported
constant is a hard Lean error; matching is by identical name). In v0.0.1
definitions and proofs are interleaved in the same files, and **every
definition module the statements need also contains a challenged theorem** —
e.g. `ReflectionSystem.lean` defines `ReflectionSystem`/`wordProd`/`W_group`
and proves 2.20/2.21/2.28/2.31; `Howlett.lean` defines `principalElement` and
proves 1.1/2.63; `MixedSign.lean` defines `MixedSignCoxeterGraph` and proves
1.5/3.5. The 52 theorems span 20 of 26 modules. Duplicating definitions
would fail comparator step 4 (shared declarations must be identical).
**Unblocking step: split modules into a definitions-only layer + theorems
layer (repo refactor, not done here).** Note also the trust caveat: unlike the
Riemann Hypothesis verification (challenge imports only Mathlib), this
challenge's trusted base would be Mathlib *plus the project's own
definitions*.

A constructed draft challenge was prepared during this verification
(`Challenge.lean`, 489 lines — all 52 statements verbatim, fully-qualified
names, `:= by sorry`, grouped by source file with `open`/`variable` context
replicated; plus a draft `comparator.json` and a 52-row manifest), but the
draft files lived in `/tmp` and were **lost when a VM/runtime restart wiped
`/tmp`** before they could be copied out. The design above is the durable
record; re-extracting the draft from the v0.0.1 sources is mechanical given
the 52-symbol set, but the files themselves will need to be rebuilt. The
draft had not been compiled (no toolchain was available when it was prepared,
and it cannot compile pre-split); `variable`/`open` replication must be
verified by building the challenge module after the split.

### 5.3 Tool availability (correction)

**`lake comparator` DOES ship with the pinned Lean 4.35.0** (release notes
2026-10-12, #14885/#15146/#15147; the standalone `leanprover/comparator` is
archived/deprecated in its favour). **No 4.36.0 toolchain is needed.** The
same holds for the bundled `lean4lean`/`nanoda`/`con-leche`/`con-ron`/
`leanchecker-paranoid`. Whether the bundled `con-leche`/`con-ron` support
`--compare` is now settled the other way: **they do not** (§4.4) — the
`--compare` mode in the con-leche README is from a `compare` branch / master
build, not the bundled binaries. The Riemann Hypothesis verification used
con-leche branch `compare` (`5dc36dc1`) built from source; reproducing that
here would mean building con-leche from source with a separate toolchain.

Exact commands once the split exists:

```bash
cd lean
lake comparator            # end-to-end, bubblewrap sandbox, Linux-only
lake comparator --paranoid # + all bundled external kernels
lake comparator --config comparator.json --challenge-from-export challenge.ndjson --solution-from-export solution.ndjson
lake check                 # challenge-less kernel replay — works today, no challenge needed
lake check --paranoid
```

con-leche cross-check (from a `compare`-branch/master build):
`.lake/build/bin/con-leche --compare challenge.ndjson solution.ndjson`.
Expected success output: `Your solution is okay!`.

## 6. Integration tips

### 6.1 NUS-Math-Formalization/coxeter

**What it is.** Lean 4 project, toolchain `leanprover/lean4:v4.7.0`, and its
`lakefile.lean` pins Mathlib to a **custom fork branch**
`trivial1711-coxeter-groups-all`, not mathlib master. That version gap (Lean
4.7.0 vs this repo's 4.35.0) means any integration with NUS is a port, not a
merge. Root `Coxeter.lean` imports only 5 files (`CoxeterMatrix.Basic`,
`CoxeterMatrix.Lemmas`, `AlternatingWord`, `BruhatOrder`, `StrongExchange`);
most of the tree (Hecke, Parabolic, Roots, GeometricRepresentation, Morphism,
…) is **not in the default lib target**. The repo is a work in progress with
open `sorry`s, not a finished library; its README file list is stale
(mentions `CoxeterMatrix1`, which is not in the tree), and files disagree
internally (`Roots.lean` uses an older structure-style `CoxeterMatrix` API
while `CoxeterMatrix.lean` defines it as a `Prop`-class).

**Conventions (NUS):** index type `α` with `[DecidableEq α]`; Coxeter matrix
entries in `ℕ` with `0 = ∞`; Coxeter system defined **axiomatically by the
exchange property** (`OrderTwoGen` + `ExchangeProp`); generators as a `Set G`
(conflating `S` with the index set, unlike Mathlib); heavy use of `List S`
words/`gprod`; `sorry`-tolerant drafting.

**Key files:** `CoxeterMatrix/CoxeterMatrix.lean` (298 lines): `class
CoxeterMatrix : Prop` over `m : Matrix α α ℕ`, fields `symmetric` and
`oneIff` (`m a b = 1 ↔ a = b`); `toRelationSet`, `toGroup := PresentedGroup
…`, `of`, `SimpleRefl`, `toSimpleRefl`, `lift`, `epsilon : G →* μ₂`.
`CoxeterMatrix/CoxeterSystem.lean` (79 lines): `class CoxeterSystem (G)
[Group G] (S : Set G) extends OrderTwoGen S` with `exchange :
ExchangeProp S` (plus `exchange'`, `deletion` derived as defaults); `class
CoxeterGroup (G) extends HOrderTwoGenGroup G`; `leftDescent`/`rightDescent`
via associated reflections. `OrderTwoGen.lean` (690 lines): `class OrderTwoGen
(S : Set G)` — generators order-2 and ≠ 1, every element a `List S` product
(`gprod`); defines `ExchangeProp`/`DeletionProp`. `Morphism.lean` (200
lines): equivalence of Coxeter systems and matrices — **contains `sorry`s**
(`alpha.even`, `constant`, `mapLift` fields). `GeometricRepresentation.lean`
(82 lines): `class Splitting (k : Matrix α α ℝ)`; `kk_aux`, `kk m`,
`sigma_star` dual action; goal lemma `order_sigma_star_mul`. **Mostly
`sorry`** (`kk.split`, `sigma_star` map proofs, `order_sigma_star_mul`,
`order_generator_mul`). `Roots.lean` (88 lines): duplicate `class split` +
`kk`, `V_S := S → ℝ`, `sigma`; **the `split` instance is `sorry`**.

**Mapping MixedSignCoxeter → NUS (concrete):**

| This repo | NUS counterpart | Fit / adaptation needed |
|---|---|---|
| `ReflectionSystem.lean`: `structure ReflectionSystem (n : ℕ)` (`B : Matrix (Fin n) (Fin n) ℝ`, `B_symm`, `B_diag_ne_zero`), `reflectionMatrix` and its involution/preservation/commutation lemmas | `GeometricRepresentation.lean`: `Splitting`, `kk`, `sigma_star`; `Roots.lean`: `split`, `sigma` | Direct conceptual match, but NUS's side is `sorry`-filled and dual-action (`V⋆`) based. Port the sorry-free `reflectionMatrix` lemmas to discharge NUS's `kk.split`/`sigma_star` sorries. **Convention clash:** NUS `kk` has diagonal `-2`, off-diagonal `+2cos(π/m)`; this repo (and the Mathlib draft) use diagonal `+2`, off-diagonal `-2cos(π/m)` — i.e. NUS `kk = -(draft geometricForm)`. Harmless for the group by `reflectionMatrix_neg` (B vs −B give the same reflections), but every form-level statement needs a sign flip. |
| `MixedSign.lean`: `Sign` (`pos`/`neg`), `MixedSignCoxeterGraph` (`sign`, `weight : Option ℕ`, `weight_symm`, `weight_ge_two`), `toBilinearForm` (diag `±2`, off-diag `-2cos(π/m)` or `-2` for ∞), `toReflectionSystem`, `negateSigns`, `isClassical` | No counterpart — NUS has no signed graphs, no `Sign`, no `weight : Option ℕ` | New NUS module (e.g. `Coxeter/MixedSign.lean`); needs NUS's `CoxeterMatrix` (ℕ entries, `0 = ∞`) extended with a sign function `α → Sign`, or a separate structure mirroring `MixedSignCoxeterGraph` over general `α` instead of `Fin n`. |
| `CoxeterPresentation.lean` + `ClassicalCoxeterDeletion.lean` + `ClassicalDeletion.lean` (Thm 3.9: deletion ⇔ exchange ⇔ Coxeter presentation; `orderCoxeterMatrix`, `theorem_3_9_coxeter_presentation`, `theorem_3_9_classical_iff_deletion/exchange`) | `Morphism.lean` (system↔matrix equivalence, `sorry`d `mapLift`); `CoxeterMatrix/Characterization.lean`, `StrongExchange.lean` | Highest-value NUS contribution: the sorry-free Matsumoto-type argument (`gamma_eq_of_reduced_of_same_length`) could complete NUS's `Morphism.mapLift` sorries. Adaptation: NUS states things over `List S` with `S : Set G`; this repo over `List (Fin n)` / `wordProd` — a translation layer is required. |
| `RootPositivity.lean` (`prop_3_10`, `root_pos_or_neg`, `exchange_of_isCoxeterForm`, `classical_graph_isClassicalCoxeter`) | `Roots.lean` (`V_S`, `sigma`, `split` — sorry'd) | Same target: prove NUS's `split` instance and root-positivity from the sorry-free local proofs. |
| `Bipartite.lean` (`BipartiteReflectionSystem`, `bipartite_conjugation_theorem`, `bipartiteConjugator`), `TreeConjugacy.lean` (Thm 2.58), `Conjugacy.lean`, `ComponentsAndTrees.lean` | `BruhatOrder.lean`, `Parabolic.lean`, `GraphSearchAux.lean` | Partial: tree conjugacy has no NUS counterpart; bipartite sign-flip is new material for NUS. `CoxeterMatrix.graph`-style graph infrastructure would need to be added to NUS first (it has none — no `SimpleGraph` Coxeter graph). |
| `Howlett.lean` (Thm 1.1, `howlettU`, `principalElement`, charpoly identity) | Nothing | New module; depends only on `ReflectionSystem`, so it ports cleanly once the reflection-system base is in. |
| `SpectralClassification.lean` / `SpectralRadius.lean` (Thms 3.27/3.28, `signature`, `spectralRadius`, `FormSpherical/FormAffine/FormIndefinite`) | Nothing (no spectral material in NUS) | New modules; note NUS has no `Matrix.PosDef` usage — would need Mathlib spectral imports, which NUS's old toolchain may lack. Lowest priority for NUS. |
| Defect-cycle family: `OddCycleSingleDefect`, `EvenCycleSingleDefect`, `TwoDefectCycle`, `CyclesAndDeletion` (Lemma 3.21 `~A_{-2}` fails deletion), `TildeAminusEvenIso`, `BipartiteDuality`, `AlternatingSquare`, `RemarksAndClassical` | Nothing | Mixed-sign-specific; no NUS home. Keep downstream; they depend only on `ReflectionSystem`/`MixedSign`/`Howlett`/`SpectralRadius`. |

**NUS sequencing (if pursued).** (1) Don't start by porting this repo to
NUS's Lean 4.7.0 + fork-Mathlib pin — either NUS upgrades its toolchain/pin
first or the port is throwaway work. (2) Highest-value, lowest-risk NUS
contribution: port the sorry-free `reflectionMatrix` lemmas to close the
`sorry`s in `GeometricRepresentation.lean` (`kk.split`, `sigma_star_*`,
`order_sigma_star_mul`) and `Roots.lean` (`split` instance), minding the sign
flip above (`kk = −geometricForm`). (3) Next: the Thm 3.9 presentation
argument to complete `Morphism.lean`'s `mapLift` sorries — this needs a
`List S` ↔ `List B` translation layer first. (4) Only then add signed-graph
material as a new `Coxeter/MixedSign.lean`, generalizing
`MixedSignCoxeterGraph` from `Fin n` to NUS's `α`. (5) Don't port
spectral/defect-cycle material to NUS — no spectral infrastructure there.
Also flag to NUS maintainers that `Roots.lean` is written against an obsolete
`CoxeterMatrix` API (`m.m`) and the README file list is stale. (Not verified:
NUS commit history / maintainer activity — freshness beyond the
`lean-toolchain`/`lakefile.lean` pins is unverified.)

### 6.2 mathlib4 — existing Coxeter material

Checked via a sparse checkout (master as of 2026-11-28). There are exactly
**4 files**, all under `Mathlib/GroupTheory/Coxeter/`:

- `Matrix.lean` — `CoxeterMatrix B` structure (symmetric `ℕ`-matrix, diagonal
  1, off-diagonal ≠ 1; **0 = ∞**); `reindex`; named finite types `Aₙ Bₙ Dₙ
  I₂ₘ E₆ E₇ E₈ F₄ G₂ H₃ H₄`.
- `Basic.lean` — `CoxeterMatrix.Group` (`PresentedGroup`), `simple`,
  `CoxeterSystem` (structure holding an isomorphism `W ≃* M.Group`),
  `IsCoxeterGroup`, `lift`, `wordProd`, `alternatingWord`. Its TODO list
  explicitly names the gaps: simple reflections distinct; **constructing
  Coxeter groups via the geometric representation**; **Matsumoto's theorem**;
  finite classification.
- `Length.lean` — `CoxeterSystem.length`, `IsReduced`, `IsLeftDescent`/
  `IsRightDescent`.
- `Inversion.lean` — `IsReflection`, `IsLeftInversion`/`IsRightInversion`,
  `leftInvSeq`/`rightInvSeq` (no duplicates for reduced words).

There is **no** `Mathlib/Geometry/Group/Coxeter/` directory, no
exchange/deletion, no geometric representation, no Coxeter graph, no Coxeter
elements, no roots. The `Bipartite.lean` TODO (lines 99–104, verified live)
still reads: "Prove that `G.IsBipartite` iff `G` does not contain an odd
cycle."

### 6.3 Status of the 11 existing upstream PRs — ALL CLOSED, none merged

Checked with `gh pr view <n> --repo leanprover-community/mathlib4` on
2026-11-28. **Every one is `CLOSED` with `mergedAt = null`, author
`jkylearmstrong`.** The 5 standalone PRs were all closed on **2026-11-27
~13:43 UTC within ~30 seconds of each other** (13:43:19–13:43:49Z); for
#46496 the timeline records the closer as maintainer `grunweg`. No closing
reason was visible in the PR page text fetched — **find out why before
re-opening anything** (check Zulip / ask the maintainer); do not assume they
were rejected on merit. Draft closed-dates were not separately verified.

| PR | State | Title | What it contributes (from PR body + `lean/MathlibDraft/` source) |
|---|---|---|---|
| #46496 | CLOSED, non-draft | feat(GroupTheory/Coxeter): add exchange and deletion properties for Coxeter systems | NEW `Mathlib/GroupTheory/Coxeter/Deletion.lean`: `CoxeterSystem.exchange` + `.deletion` via parity action on `W × Bool` and `rightInvSeq`. Draft source: `MathlibDraft/CoxeterDeletion.lean`. |
| #46497 | CLOSED, non-draft | feat(GroupTheory/Coxeter): add `ReflectionSystem` over symmetric matrices | NEW `…/Coxeter/ReflectionSystem.lean`: `ReflectionSystem ι K` (symmetric `B`, `B i i ≠ 0`), `reflectionMatrix`, involution/preservation/commutation, `group`/`toGL`. Draft source: `MathlibDraft/ReflectionSystem.lean` (generalized `ι`/`K` version of local `ReflectionSystem.lean`). |
| #46507 | CLOSED, non-draft | feat(Combinatorics/SimpleGraph): characterize bipartite graphs by absence of odd cycles | Edits `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`, resolving the live TODO above: `isBipartite_iff_forall_isCycle_even_length`, `isBipartite_iff_forall_odd_free_cycleGraph`. Draft source: `MathlibDraft/BipartiteOddCycles.lean`. |
| #46508 | CLOSED, non-draft | feat(GroupTheory/Coxeter): add `CoxeterSystem` conjugacy of Coxeter elements for acyclic Coxeter graphs | NEW `CoxeterElement.lean`: `CoxeterMatrix.graph` (`i ≠ j ∧ M i j ≠ 2`), `WordMoveStep`/`WordMoves`, all Coxeter elements conjugate for acyclic graphs. Draft source: `MathlibDraft/CoxeterElement.lean`. |
| #46513 | CLOSED, non-draft | feat(Geometry/Group/Coxeter): add spectral classification and interlacing for bipartite Coxeter elements | NEW `Mathlib/Geometry/Group/Coxeter/BipartiteSpectrum.lean` (new directory): `Matrix.BipartiteCoxeter.form/coxeter`, A'Campo classification + McMullen interlacing via `Matrix.PosDef`/`PosSemidef`. Draft source: `MathlibDraft/BipartiteSpectrum.lean`. |
| #46498 | CLOSED, draft | feat(GroupTheory/Coxeter): finiteness reduction for connected reflection systems | NEW `ReflectionSystem.lean` + `FiniteReduction.lean`: finite connected reflection systems have definite forms (`finite_connected_isDefinite`, `mixed_sign_infinite_of_isConnected`). Stacked on #46497. |
| #46505 | CLOSED, draft | feat(GroupTheory/Coxeter): add Howlett's formula for `ReflectionSystem` | NEW `Howlett.lean`: `howlettU`, `principalElement`, `U * w = -Uᵀ`, `w = -U⁻¹ * Uᵀ`, charpoly identity, over a field of char ≠ 2. Stacked on #46497. |
| #46506 | CLOSED, draft | feat(GroupTheory/Coxeter): construct `CoxeterSystem` from deletion and exchange properties | NEW `Presentation.lean`: `orderCoxeterMatrix`, `ofDeletion`/`ofExchange`, `exists_coxeterSystem_iff_hasDeletionProperty/…ExchangeProperty`. Stacked on #46496. |
| #46509 | CLOSED, draft | feat(Geometry/Group/Coxeter): prove faithfulness of the geometric representation | NEW `GeometricRep.lean`: Tits geometric representation (`geometricForm`, `geometricReflection`, `geometricRep`), root positivity, exact braid orders, faithfulness; corollaries `simple_injective`, `orderOf (simple i * simple j) = M i j` (closes two `Basic.lean` TODOs). Stacked on #46506. |
| #46510 | CLOSED, draft | feat(GroupTheory/Coxeter): add sign-flip conjugation for bipartite reflection systems | NEW `Bipartite.lean`: `IsBipartition`, `signFlip`, `negDiag`, `P * B * P = -negDiag B`, word conjugacy + charpoly invariance, `s₊s₋ ~ s₋s₊`. Stacked on #46497. |
| #46512 | CLOSED, draft | feat(GroupTheory/Coxeter): add subdiagram relation transfer for reflection systems | NEW `ParabolicTransfer.lean`: induced `ReflectionSystem` on subdiagrams, relation transfer both ways (`prod_map_reflectionMatrix_eq_of_submatrix`, `…_submatrix_eq_of_map`, `…_eq_iff_submatrix`). Stacked on #46497. |

**Nothing is upstreamed or in flight anymore** — all 11 are closed
unmerged, so the work must be re-opened (after learning why they were
closed), not continued. The local staging area `lean/MathlibDraft/` (a second
`lean_lib` in `lean/lakefile.toml`) still holds all 11 files and is the source
of truth for re-opening.

### 6.4 Concrete tips for mathlib4 (ordered, actionable)

**A. First, resolve the closure question.** All 11 PRs were batch-closed by
a maintainer on 2026-11-27 with no reason visible on the PR pages. Before
re-opening, ask on Zulip / in a comment what the blocker was (AI-use
disclosure, style, scope, CI?). Re-opening blind risks a second batch
closure.

**B. Re-open in dependency order, one stack at a time.** Dependency graph
from `MathlibDraft/*.lean` imports: (1) `ReflectionSystem` (#46497) → (2a)
`FiniteReduction` (#46498), `Howlett` (#46505), `Bipartite` sign-flip
(#46510), `ParabolicTransfer` (#46512); (2b) `CoxeterDeletion` (#46496) →
`Presentation` (#46506) → `GeometricRep` (#46509); standalone anytime:
`BipartiteOddCycles` (#46507), `CoxeterElement` (#46508),
`BipartiteSpectrum` (#46513). Suggested first wave: #46497 + #46507 + #46508
(independent, smallest, and #46507 closes a literal TODO). Second wave:
#46496 → #46506 → #46509 (the chain that closes the `Basic.lean` TODOs).
Third: the four #46497 dependents.

**C. When re-opening, rewrite imports off `MathlibDraft`.** Every draft file
does `public import MathlibDraft.ReflectionSystem` (etc.). In the PR, those
must become `Mathlib.GroupTheory.Coxeter.ReflectionSystem` (and `MathlibDraft`
must not be a dependency of any Mathlib PR — it is a local staging lib only).
Keep `lean/MathlibDraft/` in this repo as the staging area until each piece
lands, then delete the landed file from it so the two copies can't drift.

**D. Name-collision / duplication checklist (resolve before re-opening):**
1. `ReflectionSystem`: local `MixedSignCoxeter.ReflectionSystem (n : ℕ)` over
   `Fin n`/`ℝ` vs draft `ReflectionSystem ι K` — same name, generalized.
   After #46497 lands, delete the local structure and instantiate `ι := Fin
   n`, `K := ℝ` in `MixedSignCoxeterGraph.toReflectionSystem`; audit all 26
   local modules for the old `Fin n`-only API.
2. `orderCoxeterMatrix` exists in **both** local `CoxeterPresentation.lean`
   and draft `Presentation.lean` (`CoxeterSystem.orderCoxeterMatrix`) — unify
   on the draft's version; local `theorem_3_9_coxeter_presentation` should be
   re-proved from draft `orderCoxeterLift_injective_of_deletion`.
3. Local `altWord` (`CoxeterPresentation.lean`) vs Mathlib
   `CoxeterSystem.alternatingWord` — use Mathlib's when upstreaming; keep
   `altWord` only downstream if needed.
4. Local `OddCycles.lean` (`isBipartite_iff_no_odd_cycle`, Prop 2.41) is
   subsumed by #46507's `isBipartite_iff_forall_isCycle_even_length` —
   re-prove the local statement from the Mathlib lemma once #46507 lands;
   don't upstream a second copy.
5. Local `SpectralClassification.lean` defines bespoke `FormSpherical`/
   `FormAffine`/`FormIndefinite`/`qf`/`HasEigenC`; draft
   `BipartiteSpectrum.lean` instead uses Mathlib's `Matrix.PosDef`/
   `PosSemidef` — follow the draft, don't upstream the bespoke predicates.
6. Local `Bipartite.lean`'s `BipartiteReflectionSystem` structure vs draft
   `Bipartite.lean`'s `IsBipartition` predicate + `signFlip` — refactor
   downstream onto the predicate form after #46510 lands.
7. `CoxeterMatrix.graph` (#46508) vs local `MixedSignCoxeterGraph` —
   different namespaces, no clash, but don't confuse them in docs: the former
   is the unsigned classical diagram, the latter the signed weighted graph.

**E. Naming conventions to follow (Mathlib).** Keep the draft's choices,
which already match Mathlib: `CoxeterSystem.*` for system-level results,
`CoxeterMatrix.*` for matrix-level (`geometricForm`, `geometricReflection`,
`graph`), `ReflectionSystem.*` for the form-based theory,
`Matrix.BipartiteCoxeter.*` for the bipartite spectral block form. File
homes: `Mathlib/GroupTheory/Coxeter/{ReflectionSystem,Deletion,Presentation,
FiniteReduction,Howlett,Bipartite,ParabolicTransfer,CoxeterElement}.lean`;
geometric representation under `Mathlib/Geometry/Group/Coxeter/GeometricRep.lean`
(new dir, same as #46513's `BipartiteSpectrum.lean`); graph combinatorics
under `Mathlib/Combinatorics/SimpleGraph/`. Doc-strings must cite
Bourbaki/Humphreys/A'Campo/McMullen as the drafts already do, and keep the
`module`/`@[expose] public section` headers (the drafts already use them).

**F. What stays downstream (not upstreamable as-is).** The mixed-sign core —
`MixedSign.lean` (`Sign`, `MixedSignCoxeterGraph`, `toBilinearForm`,
`negateSigns`), the defect-cycle family (`OddCycleSingleDefect`,
`EvenCycleSingleDefect`, `TwoDefectCycle`), `CyclesAndDeletion` (Lemma 3.21
failure of deletion), `TildeAminusEvenIso`, `BipartiteDuality`,
`AlternatingSquare`, `RemarksAndClassical`, `SpectralRadius.lean` (Thm
1.7/3.34, Ex 3.29/3.33) — is dissertation-specific (negative cycles, sign
data) with no Mathlib analogue; keep it in this repo on top of the upstreamed
base. `RankTwo`/`RankTwoRoots`/`FiniteReduction` local versions are subsumed
by the generalized drafts once those land.

## 7. What remains

1. **`lake check` and `lake check --paranoid` still need a run.** Minimum
   realistic machine: ≥16 GiB RAM, a working bubblewrap sandbox (or an
   accepted `--inadvisably-no-sandbox` run), and `TMPDIR` on a disk with >3
   GiB free — never the 512 MiB `/tmp` tmpfs. Expect the export alone to take
   60+ min and the replay hours more on this class of machine. The partial
   export from attempt 3 is preserved for the record but is incomplete and
   cannot be replayed.
2. **Comparator needs the definitions/theorems split** (§5.2) before any
   `lake comparator` / `--compare` run is possible, plus a decision on the
   52-symbol challenge set. The draft challenge files were lost to a `/tmp`
   wipe and will need to be re-extracted from the v0.0.1 sources.
3. **Find out why the 11 Mathlib PRs were closed** (§6.3) before re-opening
   any of them.
4. The `MathlibDraft` second lib was not checked here (not a default target;
   `lake check` covers only `MixedSignCoxeter`).

## 8. Evidence index

Durable evidence produced by this verification (outside the repo):

- `~/workspace/msc-verify-worker-a-evidence.md` — toolchain install, build
  log summary, sorry/axiom grep, `#print axioms` table for the 19 registry
  symbols.
- `~/workspace/msc-verify/` — Worker D notes (`WORKER-D-NOTES.md`),
  `leanchecker` sweep log, axiom-audit sweep log and per-module audit files,
  sweep scripts.
- `~/workspace/msc-verify-tmp/tmp.XXY14cgZ` — partial (incomplete)
  `lake check` export from attempt 3, 2,809,303,040 bytes, for the record.
- Logs in `/tmp` from the build (`cache_get.log`, `lake_build.log`,
  `axioms_out.log`) are ephemeral and may already be gone after the VM
  restarts during this verification; the files above are the durable record.
