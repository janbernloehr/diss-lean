import NLS.Fourier.FoldedEnergy

/-! # Linear operations on the original interval Sobolev class -/
noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- Actual differentiability holds almost everywhere on the original interval. -/
theorem HasIntervalH1Regularity.ae_differentiableAt {f : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), DifferentiableAt ℝ f x := by
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [FunctionalAnalysis.ae_differentiableAt_complex hf.1] with x hx hmem
  exact hx (by simpa using Ioc_subset_Icc_self hmem)

/-- Complex linear combinations retain classical interval H¹ regularity. -/
theorem HasIntervalH1Regularity.linearCombination {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g) (a b : ℂ) :
    HasIntervalH1Regularity (fun x => a * f x + b * g x) := by
  refine ⟨(hf.1.const_smul a).add (hg.1.const_smul b), ?_⟩
  have he : deriv (fun x => a * f x + b * g x) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => a * deriv f x + b * deriv g x) := by
    filter_upwards [hf.ae_differentiableAt, hg.ae_differentiableAt] with x hx hy
    exact ((hx.hasDerivAt.const_mul a).add (hy.hasDerivAt.const_mul b)).deriv
  exact (memLp_congr_ae he).mpr ((hf.2.const_mul a).add (hg.2.const_mul b))

end NLS.Fourier
