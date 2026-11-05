# Finite nonlinear MkCS penalty thresholds

**Submission candidate retaining the locally verified pilot.** This project adapts the finite nonlinear QUBO model in
[Quintero, Bernal, Terlaky and Zuluaga (2022)](https://doi.org/10.1007/s11128-022-03421-z),
*Characterization of QUBO reformulations for the maximum k-colorable subgraph
problem*. It formalizes a corrected, explicitly normalized statement about the
maximum k-colorable **vertex subset** of a finite graph. It makes no claim of a
new mathematical result or of Palomar acceptance.

A graph stores each undirected edge once. Binary vertex/color slots can omit
vertices; feasibility requires at most one color per selected vertex and no
common color across an edge. The penalized objective is maximized over **all**
binary slots. Its within-vertex color sum counts ordered distinct pairs, so its
coefficient `c2` corresponds to coefficient `2*c2` for an unordered sum.

The single advertised theorem, `PalomarMkCS.solution`, bundles:

- an attained maximum over the full binary domain and the exact factor-two identity;
- optimal-value equality and an auxiliary deletion repair when `c1 ≥ 1` and `2*c2 ≥ 1`;
- feasibility of every global optimizer when `c1 > 1` and `2*c2 > 1`;
- the one-color results, where `c2` may be any real;
- two actual infeasible global optimizers at the unit-edge and half-color boundaries.

The quantified empty-vertex and empty-color cases are retained. Weak value
equality does not imply that every optimizer is feasible. The repair is an
auxiliary simultaneous deletion construction, not sequential Algorithm12.
Universal necessity/iff thresholds, the linear slack model, quantum behavior,
embedding resources, solver performance and runtime claims are outside this pilot.
The precise types and mathematical definitions are in `Challenge.lean`.

`Challenge.lean` has the deliberate statement placeholder used for comparison.
The proof environment imports a separate `MkCSProofs.Definitions` with the same
model and statement, then proves the exact advertised theorem in `Solution.lean`.
It never imports the Challenge placeholder. Existing qualified CH09-S004 proofs
were reused and mechanically adapted; the current native statement review is
not a new external review or human peer review. Earlier Astra/Claude assessments
retain their qualified source scopes and are not an endorsement of this public
entry or of every assertion in the source article.

The local port build passed with Lean4.35.0 and mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The actual printed theorem axioms are
`propext`, `Classical.choice` and `Quot.sound`. The final local verification
passed: the genuine sandboxed Comparator matched the statement and completed
proof, and Lean, NanoDa and con-ron accepted the solution. This is local mechanical
verification; Palomar has not reviewed or registered this pilot.

With Lean 4.35.0 and bubblewrap on PATH, resolve the pinned dependencies, obtain
the actual import cache, then run the supplied verification script:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Tactic Mathlib.Data.Finset.Max Mathlib.Data.Fintype.Powerset Mathlib.Data.Fintype.Prod Mathlib.Basic.Real.Basic Mathlib.Algebra.BigOperators.Group.Finset.Basic
python3 scripts/verify.py --evidence-dir .lake/verification-01
```

Use a new evidence directory for each run. The script builds, prints the theorem's
transitive axioms, and invokes the real sandboxed Comparator with the toolchain's
bundled NanoDa and con-ron. It never disables the sandbox. The submitter
`comparator.json` remains separate from the locally generated kernel configuration.

David E. Bernal Neira is the confirmed formalization author and responsible
maintainer. The development and compatibility port used Codex automation;
this credit does not claim every proof was manually written. Current root/native
model identifiers and complete attributable costs are unavailable. The exact
scientific correspondence and review limits remain explicit above.

The pilot proof package is licensed under Apache-2.0; see LICENSE and NOTICE.md.
That choice applies to this separate code package. It does not relicense the
parent thesis archive, source publications, figures, data, or dependencies.
The package includes no thesis/publisher PDF or private audit history.

**Prepared for the requested submission workflow.** The proof inputs and historical
VERIFICATION.json are unchanged. This metadata refresh creates no public repository,
hosted Palomar service result, editorial verdict or registry registration. Current
policy/schema checks and exact-candidate review remain for this successor. See
PREPARATION.md and RELEASE-STATUS.md.
