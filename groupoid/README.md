# Quotient groupoids and their universal property

This package extends the structural reason and word developments with quotient groupoid operations, an operation-preserving isomorphism fixing objects, and existence and uniqueness of extensions to arbitrary lawful target groupoids. The thirteen modules comprise ten unchanged shared prerequisites and three additions: `GroupoidOperations.lean`, `GroupoidComparison.lean` and `FreeGroupoidUniversal.lean`.

The inverse comparison chooses a quotient preimage. It does not implement the manuscript's explicit reconstruction, establish the separate globally named edge comparison, or supply an executable normaliser for arbitrary graphs. Full historical labelled deduction, binding, substitution, higher identity structures and topology are outside this package.

## Replay

Use Python 3.11 or later and the complete official Linux x86-64 Lean 4.28.0 distribution identified in the [main README](../README.md#requirements). The compiler and sibling `leanchecker` must both match the recorded fingerprints. From the repository root, choose a new output directory and run:

```sh
python3 groupoid/verify_groupoid.py --lean "$LEAN" --output evidence/groupoid
```

All thirteen sources and both manifests must remain beside the verifier. It pins the two manifests, checks all source hashes, ten prerequisite pins and the declaration inventory, compiles copied sources with warnings as errors, audits 272 explicit declarations, and invokes `leanchecker --fresh --verbose Audit`. Definitions and datatypes are included in that count; the 190 inherited declarations overlap the earlier package. The allowed axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`. Fresh replay uses Lean's own kernel, not a second implementation.

The verifier creates logs and a `verification-receipt.json`. It records command templates instead of local runtime paths or the inherited environment. Compiler output may still contain local information; inspect generated logs before sharing them.

The [extended replay record](replay-evidence.json) retains the initial nine run summaries and adds successful core and supplemental-probe runs on 8 November 2026. The core run audited 272 declarations and completed fresh checker replay. Its source and verifier hashes match this package. This record is a sanitised summary, not a historical receipt or a new mathematical review.

## Separate fidelity probes

The unchanged historical [FidelityProbes.lean](reviewer/FidelityProbes.lean) tests the statements against a nontrivial target groupoid, distinct parallel edges, collapsed vertices and other specified comparisons. Its sixteen explicit declaration reports and fresh replay passed separately. Those declarations are outside the 272-entry core inventory. The core verifier does not compile or replay this file.

After the core command above succeeds, the following Linux shell commands compile and freshly replay the probe using the generated core objects. Run from the repository root with the same absolute `LEAN` path; `evidence/groupoid-fidelity` must not already exist.

```sh
(
  set -e
  mkdir evidence/groupoid-fidelity
  cp groupoid/reviewer/FidelityProbes.lean evidence/groupoid-fidelity/
  export LEAN_PATH="$PWD/evidence/groupoid-fidelity:$PWD/evidence/groupoid/checked-source"
  export PATH="$(dirname "$LEAN"):$PATH"
  cd evidence/groupoid-fidelity
  "$LEAN" -DwarningAsError=true -o FidelityProbes.olean FidelityProbes.lean
  "$(dirname "$LEAN")/leanchecker" --fresh --verbose FidelityProbes
)
```

The source prints the sixteen axiom reports during compilation. Compare them with the `groupoid-historical-fidelity-probes` entry in the extended replay record. These manual commands do not generate the private audit driver's receipt or automatically compare its report table. That driver is not distributed. Replaying a historical reviewer source is not a new independent assessment of the mathematics.

## Artifact identity and historical provenance

The source, manifests and portable verifier are unchanged from the recovered package. Their full fingerprints are recorded in [artifact-identities.json](../artifact-identities.json).

| Artifact | SHA-256 |
| --- | --- |
| Source manifest | `c2cc63e87d3405723921a4f06007cceb790a6141ac0c1fe3edcd76ecee5d6b84` |
| Declaration inventory | `9591357e70b292d69e62accc1c8150ca1d3fc7716c71163570cf792b5894539d` |
| Distributed portable verifier | `96f8c6b3a78768865859cf270f51867d254f3ed094276b250cedb45bedfc0ae9` |
| Original historical verifier, not distributed | `06c78282bc9d1d698380d580789fa1750137257481e62b4bb6335db2f070d346` |

The portable verifier supports `--check-provenance PRIVATE_FILE` for holders of the original private provenance map and all seventeen recorded inputs. The map must have SHA-256 `392ed720a58c1fc7835ac1b251f45035fde0ed6e99ed9a9ff29c363abf8cd8fe`. Neither it nor a replacement map is distributed. Empty or whitespace-only arguments are rejected; an empty JSON map fails the fingerprint check. A default run records that historical provenance was not checked. A requested provenance check succeeds only after the exact map, its inputs and final input-stability checks pass.

This differs from the top-level portable bridge and congruence verifiers, which reject `--check-provenance` altogether. The historical groupoid verifier had a different command-line interface and identity; its receipts do not attest the distributed portable verifier. No historical private receipts, omission indices or review reports are included here.
