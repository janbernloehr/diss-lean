import NLS.ComplexAnalysis.CircleSquaredBandHomotopy
/-! # Exact squared-circle pullback along a prescribed affine homotopy -/
noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem circleIntegral_squared_pullback_eq_circle_of_affine_mem
    (f : ℂ → ℂ) (D : Set ℂ) (d c : ℂ) (R r : ℝ)
    (hf : AnalyticOnNhd ℂ f D)
    (hpath : ∀ s : I, ∀ theta : ℝ,
      AffineMap.lineMap (circleMap d R theta) ((circleMap c r theta)^2) (s : ℝ) ∈ D) :
    (∮ z in C(c,r), f (z^2)*(2*z)) = ∮ z in C(d,R), f z := by
  let gamma := (circlePath c r).map (continuous_id.pow 2)
  let H := ContinuousMap.Homotopy.affine (circlePath d R : C(I,ℂ)) (gamma : C(I,ℂ))
  have hmem (s t : I) : H (s,t) ∈ D := by
    rw [ContinuousMap.Homotopy.affine_apply]
    exact hpath s ((2*Real.pi)*(t : ℝ))
  have hclosed : IsClosed (range H) := (isCompact_range H.continuous).isClosed
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ t _ => mem_range_self (s,t))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,t⟩,rfl⟩
      exact (hf _ (hmem s t)).differentiableAt)
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (squaredCirclePath_contDiffOn _ _))
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath c r) ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp heq
  exact hp.symm.trans heq.symm

end NLS.ComplexAnalysis
