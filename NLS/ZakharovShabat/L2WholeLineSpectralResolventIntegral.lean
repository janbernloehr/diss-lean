import NLS.FunctionalAnalysis.SelfAdjointCayleyResolvent
import NLS.FunctionalAnalysis.RealResolventKernel
import NLS.ZakharovShabat.L2WholeLineRealSpectralMeasure

/-! # The actual physical resolvent is represented by the transported real measure -/
noncomputable section
set_option autoImplicit false
open MeasureTheory NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The original physical nonreal inverse is exactly the Cayley resolvent functional calculus. -/
theorem wholeLineNonrealResolvent_eq_cayley_cfc (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    wholeLineNonrealResolvent u hu z hz =
      cfcHom (wholeLineCayley_isStarNormal u hu)
        (cayleyResolventFunction (spectrum ℂ (wholeLineCayley u hu))
          (wholeLineCayley_spectrum_subset_unitary u hu) z hz) :=
  selfAdjointNonrealResolvent_eq_cayley_cfc
    (wholeLineMinimalOperator_closure_isSelfAdjoint u hu) z hz

/-- The kernel is integrable against the actual transported physical measure. -/
theorem integrable_wholeLineRealSpectralMeasure_resolventKernel (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (z : ℂ) (hz : z.im ≠ 0) :
    Integrable (fun t : ℝ => (z-(t : ℂ))⁻¹) (wholeLineRealSpectralMeasure u hu v) :=
  integrable_realResolventKernel _ z hz

/-- The actual nonreal resolvent vector expectation is the Cauchy integral
of the real measure constructed from the original physical operator. -/
theorem wholeLineRealSpectralMeasure_resolvent_integral (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (v : WholeLineL2)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∫ t, (z-(t : ℂ))⁻¹ ∂wholeLineRealSpectralMeasure u hu v =
      inner ℂ v (wholeLineNonrealResolvent u hu z hz v) := by
  let μ := wholeLineCayleySpectralMeasure u hu v
  let F : spectrum ℂ (wholeLineCayley u hu) → ℝ := fun x => inverseCayleyReal x
  let r := cayleyResolventFunction (spectrum ℂ (wholeLineCayley u hu))
    (wholeLineCayley_spectrum_subset_unitary u hu) z hz
  have hm : Measurable F := measurable_inverseCayleyReal.comp measurable_subtype_coe
  have hf : AEStronglyMeasurable (fun t : ℝ => (z-(t : ℂ))⁻¹) (μ.map F) :=
    (continuous_realResolventKernel z hz).aestronglyMeasurable
  have hae : ∀ᵐ (x : spectrum ℂ (wholeLineCayley u hu)) ∂μ, (x : ℂ) ≠ 1 := by
    rw [ae_iff]
    simpa only [not_not] using wholeLineCayleySpectralMeasure_one_fiber_zero u hu v
  change (∫ t, (z-(t : ℂ))⁻¹ ∂μ.map F) = _
  rw [integral_map hm.aemeasurable hf]
  calc
    (∫ x, (z-(F x : ℂ))⁻¹ ∂μ) = ∫ x, r x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      exact (cayleyResolventFunction_eq_inverse _ _ z hz x hx).symm
    _ = inner ℂ v (cfcHom (wholeLineCayley_isStarNormal u hu) r v) :=
      integral_wholeLineCayleySpectralMeasure u hu v r
    _ = inner ℂ v (wholeLineNonrealResolvent u hu z hz v) := by
      rw [wholeLineNonrealResolvent_eq_cayley_cfc]

end NLS.ZakharovShabat
