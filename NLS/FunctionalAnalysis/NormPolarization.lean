import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

/-- Two real linear maps with identical norms have identical real parts
of their complex inner products. The domain needs no inner product. -/
theorem re_inner_map_eq_of_norm_map_eq
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [NormedSpace ℝ G]
    (U : E →L[ℝ] F) (V : E →L[ℝ] G) (hn : ∀ x, ‖U x‖ = ‖V x‖) (x y : E) :
    RCLike.re (inner ℂ (U x) (U y)) = RCLike.re (inner ℂ (V x) (V y)) := by
  have h := congrArg (fun t : ℝ => t^2) (hn (x+y))
  rw [map_add,map_add,norm_add_sq (𝕜 := ℂ),norm_add_sq (𝕜 := ℂ),hn x,hn y] at h
  linarith

end NLS.FunctionalAnalysis
