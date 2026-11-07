# Source-to-proof correspondence

This local candidate proposes an extension/version of the registered nonlinear MkCS family. The original thesis PDF is the authority for the thesis statements; recovered text and article material have their own provenance. Prior source and compiler qualifications retain their own scopes. The current complete packet passed the bounded mkcs02 builds, axiom census and genuine Comparator/Lean/NanoDa/con-ron checks, followed by SATISFACTORY independent package/interface review; exact evidence and unchanged proof/compiler hashes are bound in VERIFICATION.json. This documentary successor awaits independent closeout and final source freeze, and has no version 2 public/hosted/service/registration result.

The written Algorithm12 deletes one currently occupied slot from an active edge conflict, then scans slots for a second occupied color on the same vertex. The formal `edgeScan` and `rowScan` update the selection after every deletion. Edge lists are sound and exhaustive, slot lists exhaustive; order and repetitions remain quantified.

| Component | Existing complete theorem | Source/qualification |
| --- | --- | --- |
| LinearBinaryMaximum | `Chapter09.Source.qLinear_binary_maximum` | The full binary real-array domain attains exactly the finite Boolean-state optimum. |
| LinearStrict | `Chapter09.Source.theorem_9_3_1` | Source strict linear theorem, including positive color count and arbitrary joint binary slacks. |
| LinearWeakValue | `Chapter09.Source.qLinear_eq_alpha` | Weak unit linear penalties give value equality; every optimizer is not asserted feasible. |
| LinearOneColorValue | `Chapter09.Source.qLinear_one_color` | At one color the linear row-slack coefficient is still required nonnegative. |
| LinearOneColorStrict | `Chapter09.Source.linear_one_color_strict` | Strict edge penalty and nonnegative row-slack penalty give one-color optimizer feasibility. |
| NonlinearSourceAlgorithm | `Chapter09.Sequential.corollary_9_3_1` | Original unit-boundary nonlinear corollary with the actual exhaustive current-state Algorithm12. |
| LinearSourceAlgorithm | `Chapter09.Source.corollary_9_3_2` | Original unit-boundary linear corollary with actual current-state Algorithm12. |
| NonlinearWeakAlgorithm | `Chapter09.Sequential.algorithm_nonlinear_repaired` | Actual sequential nonlinear repair at the corrected weak ordered threshold 2*c2>=1. |
| NonlinearOneColorAlgorithm | `Chapter09.Sequential.algorithm_nonlinear_k1` | The one-color nonlinear sequential repair imposes no hypothesis on the color coefficient. |
| LinearWeakAlgorithm | `Chapter09.Source.algorithm_linear` | Actual sequential linear repair at both weak unit thresholds, for every joint maximizer. |
| LinearOneColorAlgorithm | `Chapter09.Source.algorithm_linear_one_color` | One-color linear sequential repair retains nonnegative row-slack coefficient. |
| NonlinearUniversalValue | `Chapter09.Source.nonlinear_universal_value_iff` | For fixed positive k and positive coefficients, characterize value equality over every n and graph. |
| LinearUniversalValue | `Chapter09.Source.linear_universal_value_iff` | Universal linear value equality has the one-color exception and unit multi-color threshold. |
| SourceRouteStrict | `Chapter09.SourceProcedure.theorem_9_3_2_from_text` | Same strict nonlinear source theorem through the accepted manuscript-route proof; no new theorem credit. |

## Original source and explicit changes

- Thesis equations9.9–9.12 and Theorem9.3.1: retain actual joint binary `x,s,t`, the full literal squared residuals, finite attainment, `k>0` and `c1,c2>1`. The strict linear result follows the accepted canonical-lift replacement proof; the defective orientation-dependent printed map9.11 is not certified.
- Thesis Algorithm12 and Corollaries9.3.1–2: retain source unit-boundary clauses and positive color count in their literal interfaces. Additional weak-threshold endpoints expose already accepted stronger repaired results separately, without changing the source corollary interfaces.
- The ordered nonlinear sum has effective unordered weight `2*c2`; weak value/sequential repair uses `c1>=1, 2*c2>=1`. Strict effective weights make every optimizer feasible. The one-color nonlinear branch allows arbitrary real `c2`; the linear branch retains `c2>=0` for arbitrary binary row slacks.
- Thesis Propositions9.3.1–2 and Remark9.3.1: the complete universal value statements fix positive `k` and positive coefficients, then quantify over every vertex count and graph. Nonlinear equality is equivalent to `c1>=1` and `(k=1 or c2>=1/2)`; linear equality is equivalent to `c1>=1` and `(k=1 or c2>=1)`. These do not assert necessity separately on each individual graph.
- The accepted Chapter09SourceProcedure companion proves the same full strict nonlinear Theorem9.3.2 type with the original stronger `c1,c2>1` hypotheses by choosing one active conflict, erasing one selected slot, using a gain of `weight-1`, contradicting maximality, then using attained feasible cardinality. Its ordered color weight is exactly `2*c2`; the defective printed equality missing that factor is not reinstated. Accepted simultaneous-cover alternative proofs remain unchanged in the copied library.

## Nonvacuity and trust boundary

The binary state domains are finite and inhabited, including empty vertex/edge sets. `qLinear_binary_maximum` proves actual attainment over separately quantified real binary arrays, not an assumed optimizer oracle. The source library contains empty/one-color/nontrivial-edge and threshold-boundary controls. This candidate adds no optimizer, feasibility, KKT or source-theorem axiom.

The actual full-root comparison passed, and the independent review checked old and new theorem types, complete computational definitions, current-state list scan semantics, nonvacuity and degenerate domains against the retained source orientation and actual transitive-axiom evidence. Only Classical.choice, Quot.sound and propext occur in the compared completed roots. The reviewer inspected the actual coordinator receipts rather than rerunning proofs. Independent documentary closure, final validation/freeze and version 2 external stages remain pending. No historical benchmark, numerical performance, quantum behavior, complexity bound or unchanged-slack linear monotonicity is advertised.

## Exact public source copies

All eleven proof modules are byte-identical to the published archive members listed in PROVENANCE.json. Version1 used renamed compatibility ports; version2 uses current canonical source layout. The original named nonlinear proposition bundle and complete conjunction are unchanged. New proposition wrappers fully restate accepted types, and their completed wrappers reference only existing proofs. Challenge imports Mathlib alone, never these project sources; Solution never imports Challenge.
