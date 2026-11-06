import NLS.Articles.KdVConvexity.GlobalSpectralActions
import NLS.Articles.KdVConvexity.PositiveActionNorm
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughGroundEnergyFiniteGap
import NLS.KdV.HillHminusPhysicalArnoldActions
import NLS.KdV.HillHminusPhysicalSourceDensity

/-! # The actual positive coordinate calibration at every real rough potential

Original physical source density and continuity identify the intrinsic
Arnold map with the quadratic positive forward calibration on all real
Hminus1 sources. The action norm is exactly the positive Hilbert norm squared.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

theorem global_Arnold_positive_calibration
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (I q).val (actionIndexEquiv.symm n) =
      (((1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2 : ℝ) : ℂ) := by
  let F : PeriodOneRealHminusOne → ℂ := fun a => (I a.val).val (actionIndexEquiv.symm n)
  let G : PeriodOneRealHminusOne → ℂ := fun a =>
    (((1+(n : ℝ))*‖D.positive a.val (n : ℤ)‖^2 : ℝ) : ℂ)
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (WeightedCoeff.evalCLM baseActionWeight 1 (actionIndexEquiv.symm n)).continuous.continuousAt.comp
      ((hI a.val (hΩ a.property)).continuousAt.comp continuous_subtype_val.continuousAt)
  have hG : Continuous G := by
    have hD : Continuous (fun a : PeriodOneRealHminusOne => D.positive a.val) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      exact (D.positive_analytic a.val (D.real_mem_domain a.val a.property)).continuousAt.comp
        continuous_subtype_val.continuousAt
    have hc : Continuous (fun a : PeriodOneRealHminusOne => D.positive a.val (n : ℤ)) :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).continuous.comp hD
    exact Complex.continuous_ofReal.comp (continuous_const.mul (hc.norm.pow 2))
  have he : F = G := denseRange_hillPhysicalHminusEmbedding.equalizer hF hG (by
    funext p
    change (I (hillOriginalHminusSource p.val)).val (actionIndexEquiv.symm n) = _
    rw [hrec _ (hillOriginalHminusSource_real p.val p.property.2) n,
      hillHminusRealGapContourMoment_original_source,
      D.positive_physical_action_norm p (n : ℕ) n.property]
    rfl)
  exact congrFun he (⟨q,hr⟩ : PeriodOneRealHminusOne)

theorem global_Arnold_norm_eq_positive_norm_sq
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ‖I q‖ = ‖D.positive q‖^2 :=
  norm_action_eq_positive_norm_sq (I q) (D.positive q)
    (D.positive_zero q (D.real_mem_domain q hr))
    (global_Arnold_positive_calibration D Ω hΩ I hI hrec q hr)


end NLS.Articles.KdVConvexity
