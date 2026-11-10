# Formal verification sources

Lean developments accompanying *The Functional Interpretation of Logical Deduction*. This repository contains sixteen distinct core source modules for selected calculi, their verification scripts and source inventories. The separate `groupoid/` package contains thirteen modules: ten unchanged copies of shared prerequisites and three additional modules. It does not formalise the whole book or the full historical labelled natural deduction calculus.

## Mathematical scope

| Sources | Results and limits |
| --- | --- |
| `StructuralReasons.lean` | Termination of selected eight-rule and ten-rule relations on endpoint-indexed structural reason trees over an arbitrary graph. |
| `ReducedWords.lean`, `StructuralInvariant.lean`, `StructuralNormalForms.lean`, `StructuralConfluence.lean` | Confluence, reachable unique normal forms and reduced-spine classification for the ten-rule structural relation. |
| `WordNormalisation.lean`, `TypedWordBridge.lean` | Ordinary adjacent-inverse cancellation and its comparison with the structural invariant, preserving endpoints and parallel edge identities. |
| `ReasonCongruence.lean`, `EightRuleCounterexample.lean`, `ReasonQuotient.lean` | Equality of the generated eight-rule and ten-rule congruences, comparison with typed word equivalence, a specified eight-rule nonconfluence example and a bijection of fixed-endpoint quotient hom-sets. |
| `groupoid/GroupoidOperations.lean`, `groupoid/GroupoidComparison.lean`, `groupoid/FreeGroupoidUniversal.lean` | Quotient groupoid operations, an operation-preserving object-fixing isomorphism, and existence and uniqueness of extensions to arbitrary lawful target groupoids. |
| `ImplicationSchemas.lean` | Boolean soundness and a nonderivability result for the stated formula-level Hilbert reconstruction. This is not historical labelled adequacy or normalisation. |
| `ProductFragment.lean` | Termination, confluence and unique normal forms for raw pairing and projection trees. Its normaliser and equality decision procedure require decidable equality of atoms. |
| `EqualitySkeleton.lean` | Termination and nonconfluence of the specified raw 37-rule equality-reason skeleton. Dependent typing, substitution and binding are not encoded. |

The structural word normaliser uses classical, noncomputable definitions. The original ten-module quotient comparison gives a bijection of hom-sets. The [groupoid extension](groupoid/README.md) adds operations, their preservation and the universal property. Its inverse chooses a quotient preimage; it does not implement the manuscript’s explicit reconstruction or compare the dependent-edge encoding with globally named edges. Definitions, hypotheses and exact theorem statements are in the source files. Declaration inventories include definitions and datatypes as well as theorems; their counts are not counts of distinct mathematical results.

The later global-edge, explicit-reconstruction, typed computational core, named representation, structural alpha-equivalence, named substitution and binder-freshness packages described in the working manuscript are not included. Their complete source and evidence packages remain unavailable in the recovered material. No replay of those packages is claimed here.

## Results and declarations

The following map identifies entry points for the available formal results.
The declarations use the syntax and hypotheses of their own modules; the
map does not assert an unproved correspondence with the full book calculus.

| Result described in the book | Source and declarations |
| --- | --- |
| Termination of the eight- and ten-rule structural relations | [`StructuralReasons.lean`](StructuralReasons.lean): `StructuralReasons.terminating` and `StructuralReasons.no_infinite_reduction`, with the `complete` parameter selecting the relation. |
| Confluence and reachable normal forms for the ten-rule relation | [`StructuralConfluence.lean`](StructuralConfluence.lean): `StructuralReasons.ten_confluent` and `StructuralReasons.ten_exists_unique_normal`. |
| Comparison of the structural congruences and words | [`ReasonCongruence.lean`](ReasonCongruence.lean): `StructuralReasons.ReasonCongruence.eight_iff_ten` and `StructuralReasons.ReasonCongruence.iff_typed_word_equiv`. |
| Free-groupoid extension property | [`groupoid/FreeGroupoidUniversal.lean`](groupoid/FreeGroupoidUniversal.lean): `StructuralReasons.FreeGroupoid.reason_universal` and `StructuralReasons.FreeGroupoid.word_universal`. |
| Boolean soundness of the selected formula systems | [`ImplicationSchemas.lean`](ImplicationSchemas.lean): `ImplicationSchemas.selected_sound`. |
| Confluence and unique normal forms for raw products | [`ProductFragment.lean`](ProductFragment.lean): `ProductFragment.confluent` and `ProductFragment.exists_unique_normal`. |
| Termination and nonconfluence of the raw equality skeleton | [`EqualitySkeleton.lean`](EqualitySkeleton.lean): `EqualitySkeleton.terminating` and `EqualitySkeleton.not_confluent`. |

## Requirements

Use Python **3.11 or later** and Lean **4.28.0**. The Python scripts use only the standard library. Lean imports its bundled `Std.Tactic` and local modules; there are no external Lean package dependencies. Keep the complete Lean distribution, including its libraries and `leanchecker`, together. The scripts do not install a toolchain.

The bridge, congruence and groupoid procedures require the official Linux x86-64 release, commit `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`. Obtain the distribution from [Lean's v4.28.0 release](https://github.com/leanprover/lean4/releases/tag/v4.28.0), specifically [lean-4.28.0-linux.tar.zst](https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-linux.tar.zst).

| Artifact | SHA-256 |
| --- | --- |
| Release archive, 520,948,633 bytes | `ceb3a3f844f7aebf63245e2b51c28d5b0ed38942c19f93cf3febd520302160bd` |
| `bin/lean` | `3e0d0d3d801675359f2d4cf9815bfdb417b20b92fdd9d48b3b14c95bbae28bbf` |
| `bin/leanchecker` | `cb6cee24e93aa1d72ad0314906c51918f7c96947e18790a0273c837c25e79025` |
| Extracted distribution tree, using the method below | `e8433dd0e8c0a676f4cae4033f4280feb92ee75dc5dede320b98acd77d4efbf6` |

The bridge verifier pins the compiler and records the checker's identity; the congruence and groupoid verifiers pin both. The original structural, implication, product and confluence scripts check the Lean version, with different recorded identity checks. These distinctions are preserved in this distribution.

## Run the checks

Run from a disposable copy of this repository. Set `LEAN` to the absolute path of the installed Linux compiler. The first command creates `build/`; it can overwrite earlier structural output. Each named output directory below must be new for a fresh run.

```sh
export LEAN=/path/to/lean-4.28.0-linux/bin/lean
python3 verify.py --lean "$LEAN"
python3 verify_implication.py --lean "$LEAN" --output-dir evidence/implication
python3 verify_product.py --lean "$LEAN" --output-dir evidence/product
python3 verify_confluence.py --lean "$LEAN" --output evidence/confluence
python3 verify_bridge.py --lean "$LEAN" --output evidence/bridge
python3 verify_congruence.py --lean "$LEAN" --output evidence/congruence
python3 groupoid/verify_groupoid.py --lean "$LEAN" --output evidence/groupoid
python3 verify_equality_skeleton_portable.py --lean "$LEAN" --output-dir evidence/equality-linux
```

Each command compiles with warnings treated as errors, checks its named axiom reports and writes logs and a `verification-receipt.json`. The bridge, congruence, groupoid and separate equality-skeleton replay additionally invoke `leanchecker --fresh`, using Lean's own kernel in a fresh environment. This is not an independent kernel implementation. The earlier four commands in this block do not invoke that fresh checker. `lake build` alone builds only `StructuralReasons` and does not replace these checks.

The disclosed axiom dependencies are subsets of `propext`, `Classical.choice` and `Quot.sound`, as recorded per declaration. Kernel acceptance checks the encoded presentation; correspondence with a calculus in the book requires mathematical review. Locally generated receipts contain local paths and environment information and are ignored by Git.

The [initial sanitised replay record](replay-evidence.json) identifies the toolchain, sources, verifier variants, declaration-level dependency reports and results of runs on 8 November 2026 before the groupoid source package was recovered. Its groupoid exclusion describes that earlier run. The record is preserved unchanged. It distinguishes ordinary compilation from `leanchecker --fresh`, and the separately compiled Linux equality skeleton from the historical Windows verifier. It omits local paths and does not replace the full private receipts or an independent assessment of the formal statements.

The [extended record](groupoid/replay-evidence.json) repeats those nine summaries and adds the recovered groupoid package's 272-declaration core replay and a separate 16-declaration fidelity-probe replay. The [supplemental source and commands](groupoid/README.md#separate-fidelity-probes) are separate from the core verifier and the sixteen distinct core source modules.

### Equality skeleton: historical Windows verifier

`verify_equality_skeleton.py` requires the exact historical Windows-native Lean executable with SHA-256 `6a66c4a5739fa17146b88ac81bab2bca1924806cac321ddad6b96006dde9c691`. A Linux executable, or another executable reporting 4.28.0, will be rejected. That Windows executable is not distributed here, and this repository does not provide an acquisition route for it.

For holders of that executable, from a fresh repository copy in PowerShell:

```powershell
$env:LEAN = 'C:\path\to\matching\lean.exe'
python verify_equality_skeleton.py --lean $env:LEAN --output-dir evidence/equality-windows
```

`verify_equality_skeleton_portable.py` supplies a separate fresh replay of the
same source on the official Linux release pinned above. It checks the source,
historical verifier, compiler, checker and complete distribution-tree hashes,
compiles a fresh copy in a
new output directory, compares the declaration dependency reports with the
historical audit and runs `leanchecker --fresh`. Its receipt identifies this
procedure separately and does not claim that the historical Windows verifier
ran. The tree hash covers each regular file's relative name and SHA-256, and
each symlink's relative name and target, sorted by name. For each entry it
hashes `kind`, NUL, name, NUL, digest or target, and a newline; `kind` is `f`
for a file and `l` for a symlink. The recorded value was compared with every
entry of the release archive whose hash appears above.
The checker must be beside the compiler; loader override variables are removed
from their subprocess environment. System libraries outside the distribution
are not covered. The script accepts
explicit compiler, checker and tree hashes for another Lean 4.28.0
distribution; those hashes and the release must be verified by the reader.
The included pins and replay evidence are for Linux x86-64.

To compare an extracted Linux distribution with the pinned release archive,
install `unzstd` and run the separate archive check:

```sh
python3 verify_release_tree.py --archive /path/to/lean-4.28.0-linux.tar.zst \
  --toolchain-root /path/to/lean-4.28.0-linux
```

The check verifies the archive hash before reading it and compares the names,
file contents and symlink targets with the installed tree. It does not extract
or modify the archive or toolchain.

The [portable replay record](equality-portable-replay-evidence.json) records a
Linux run of the new script, including the source, toolchain, object and log
hashes and the declaration-level dependencies. The raw logs and local paths
are not distributed with that record.

## Artifact identity and provenance

The thirteen top-level Lean sources are byte-for-byte copies of the retained formal source snapshot. All thirteen sources in `groupoid/` are byte-for-byte copies of the separately recovered package; ten match the shared top-level sources. [artifact-identities.json](artifact-identities.json) gives their complete SHA-256 fingerprints and the original and distributed fingerprints of each copied input. The source manifests and declaration inventories are unchanged.

`verify_bridge.py` and `verify_congruence.py` are **portable-v1** variants. They omit `input-fingerprints.json`, which described private historical inputs, and remove its optional path-checking loop. They retain `--check-provenance` only to reject it explicitly before tool access or output creation. No empty or sanitised provenance map is accepted as evidence of a successful historical-path check. Their receipts state `original_provenance_paths_checked: false` and `verifier_variant: portable-v1`. The congruence docstring is also updated. All mandatory source-manifest, baseline-source, inventory, compiler, declaration-audit, input-stability and fresh-replay checks are retained. The other five verifiers are unchanged.

The recovered `groupoid/verify_groupoid.py` is unchanged from its retained portable version. It differs from the original historical groupoid verifier and supports a separately supplied, exactly pinned private provenance map; see its [package guide](groupoid/README.md).

The two modified top-level scripts have different identities from the historical scripts named in the manuscript. Historical receipts do not attest these modified bytes. This repository contains no historical private receipts or review reports; its identity manifest is not itself evidence of a successful compilation or independent review.

No book TeX, PDF, original correspondence, compiler binaries or compiled proof objects are included. No licence is granted by this repository; licensing remains undecided.
