import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Analytic extension at infinity of bounded exterior functions -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- A bounded analytic exterior function becomes analytic at zero after
inversion and filling its removable singularity. The extension agrees at
every nonzero point of an explicit disc. -/
theorem exists_analytic_inversion_extension_of_exterior_bound
    (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | R < ‖z‖})
    (hb : ∀ z : ℂ, R < ‖z‖ → ‖f z‖ ≤ M) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 R⁻¹) ∧
      ∀ z ∈ ball (0 : ℂ) R⁻¹, z ≠ 0 → g z = f z⁻¹ := by
  let h : ℂ → ℂ := fun z => f z⁻¹
  have hlarge (z : ℂ) (hz : z ∈ ball (0 : ℂ) R⁻¹ \ {0}) : R < ‖z⁻¹‖ := by
    have hz0 : z ≠ 0 := hz.2
    have hsmall : ‖z‖ < R⁻¹ := by simpa only [mem_ball, dist_zero_right] using hz.1
    rw [norm_inv]
    exact (lt_inv_comm₀ (norm_pos_iff.mpr hz0) hR).mp hsmall
  have hd : DifferentiableOn ℂ h (ball 0 R⁻¹ \ {0}) := by
    intro z hz
    exact ((hf z⁻¹ (hlarge z hz)).differentiableAt.comp z
      (differentiableAt_inv (show z ≠ 0 from hz.2))).differentiableWithinAt
  have hbounded : BddAbove (norm ∘ h '' (ball 0 R⁻¹ \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hb z⁻¹ (hlarge z hz)
  let g := Function.update h 0 (limUnder (𝓝[≠] 0) h)
  have hg : DifferentiableOn ℂ g (ball 0 R⁻¹) :=
    differentiableOn_update_limUnder_of_bddAbove
      (isOpen_ball.mem_nhds (mem_ball_self (inv_pos.mpr hR))) hd hbounded
  refine ⟨g, ?_, ?_⟩
  · exact hg.analyticOnNhd isOpen_ball
  · intro z _ hz
    exact Function.update_of_ne hz _ _

end NLS.ComplexAnalysis
