module

public import MkCSProofs

/-! Complete wrappers over existing accepted proofs; Challenge is never imported. -/
public section
namespace PalomarMkCS


theorem solution : Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Chapter09.Source.qNonlinear_binary_maximum
  · exact Chapter09.Source.orderedProducts_eq_twice
  · exact Chapter09.Source.qNonlinear_eq_alpha
  · exact Chapter09.Source.nonlinear_optimizer_repair
  · exact Chapter09.Source.nonlinear_optimizer_strict
  · exact Chapter09.Source.qNonlinear_one_color
  · exact Chapter09.Source.nonlinear_one_color_strict
  · exact Chapter09.Source.nonlinear_one_color_repair
  · exact Chapter09.Source.Controls.unit_edge_global_tie
  · exact Chapter09.Source.Controls.half_color_global_tie


theorem extension_solution : ExtensionStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact @Chapter09.Source.qLinear_binary_maximum
  · exact @Chapter09.Source.theorem_9_3_1
  · exact @Chapter09.Source.qLinear_eq_alpha
  · exact @Chapter09.Source.qLinear_one_color
  · exact @Chapter09.Source.linear_one_color_strict
  · exact @Chapter09.Sequential.corollary_9_3_1
  · exact @Chapter09.Source.corollary_9_3_2
  · exact @Chapter09.Sequential.algorithm_nonlinear_repaired
  · exact @Chapter09.Sequential.algorithm_nonlinear_k1
  · exact @Chapter09.Source.algorithm_linear
  · exact @Chapter09.Source.algorithm_linear_one_color
  · exact @Chapter09.Source.nonlinear_universal_value_iff
  · exact @Chapter09.Source.linear_universal_value_iff
  · exact @Chapter09.SourceProcedure.theorem_9_3_2_from_text

end PalomarMkCS
