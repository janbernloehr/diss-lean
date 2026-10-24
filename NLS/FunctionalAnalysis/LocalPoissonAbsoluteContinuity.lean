import NLS.FunctionalAnalysis.RealPoissonBounds
import NLS.FunctionalAnalysis.PoissonAbsoluteContinuity

/-! # Local Poisson bounds imply absolute continuity on smaller intervals -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace NLS.FunctionalAnalysis

/-- Bounds for centers in a larger interval and only for small positive heights
suffice for absolute continuity of the measure on the smaller closed interval. -/
theorem absolutelyContinuous_restrict_Icc_of_local_poisson_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a b δ η : ℝ) (C : ℝ≥0)
    (hδ : 0 < δ) (hη : 0 < η)
    (h : ∀ x ∈ Ioo (a-δ) (b+δ), ∀ ε : ℝ, 0 < ε → ε < η →
      (∫ t, realPoissonKernel x ε t ∂μ) ≤ C) :
    μ.restrict (Icc a b) ≪ (volume : Measure ℝ) := by
  let ν := μ.restrict (Icc a b)
  let M := μ.real univ
  have hmass : ν.real univ ≤ M := by
    rw [measureReal_restrict_apply_univ]
    exact measureReal_mono (subset_univ _)
  let B : ℝ≥0 := ⟨max (C : ℝ) (max (M/(2*δ)) (M/η)), le_trans C.coe_nonneg (le_max_left _ _)⟩
  apply absolutelyContinuous_volume_of_poisson_bound ν B
  intro x ε hε
  have hle : (∫ t, realPoissonKernel x ε t ∂ν) ≤ ∫ t, realPoissonKernel x ε t ∂μ :=
    setIntegral_le_integral (integrable_realPoissonKernel μ x ε hε)
      (Filter.Eventually.of_forall (fun t => realPoissonKernel_nonneg x ε t hε.le))
  by_cases hx : x ∈ Ioo (a-δ) (b+δ)
  · by_cases he : ε < η
    · exact (hle.trans (h x hx ε hε he)).trans (le_max_left _ _)
    · have hb : (∫ t, realPoissonKernel x ε t ∂ν) ≤ M/η := by
        apply hle.trans ((integral_realPoissonKernel_le_inv_height μ x ε hε).trans ?_)
        exact div_le_div_of_nonneg_left (measureReal_nonneg) hη (le_of_not_gt he)
      exact hb.trans ((le_max_right _ _).trans (le_max_right _ _))
  · have hd : ∀ᵐ t ∂ν, δ ≤ |x-t| := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rcases le_or_gt x (a-δ) with hxleft | hxleft
      · exact (by linarith [ht.1] : δ ≤ -(x-t)).trans (neg_le_abs _)
      · have hxright : b+δ ≤ x := by
          by_contra hn
          exact hx ⟨hxleft,lt_of_not_ge hn⟩
        exact (by linarith [ht.2] : δ ≤ x-t).trans (le_abs_self _)
    have hb : (∫ t, realPoissonKernel x ε t ∂ν) ≤ M/(2*δ) :=
      (integral_realPoissonKernel_le_of_ae_distance ν x ε δ hε hδ hd).trans
        (div_le_div_of_nonneg_right hmass (by positivity))
    exact hb.trans ((le_max_left _ _).trans (le_max_right _ _))

end NLS.FunctionalAnalysis
