import NLS.Articles.KdVConvexity.GlobalArnoldCalibration
import NLS.Articles.KdVConvexity.CoordinateActionExtension
import NLS.KdV.HillRoughPairInverse

/-! # Actual normalized local coordinate inverses and their Arnold-action identity -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV NLS.Articles.KdVKdV2Frequencies

theorem Arnold_action_of_pair_inverse_identity
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ Coeff.realPairLocus 2)
    (hi : D.signed q = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted actionIndexEquiv z)) :
    I q = normalizedCoordinateActions z := by
  apply Subtype.ext
  funext k
  have hc := global_Arnold_positive_calibration D Ω hΩ I hI hrec q hr (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply] at hc
  have hp : D.positive q ((actionIndexEquiv k : ℕ+) : ℤ) =
      (signedPairToDeleted actionIndexEquiv z).val (positiveIndexInjection actionIndexEquiv k) := by
    rw [signedPairToDeleted_positive]
    exact positive_eq_signedPair_of_inverse_identity D actionIndexEquiv q hr z hi k
  rw [hc,hp,norm_signedPairToDeleted_positive_sq actionIndexEquiv z hz k]
  have hx : z.1 k = ((z.1 k).re : ℂ) := Complex.ext rfl (hz.1 k)
  have hy : z.2 k = ((z.2 k).re : ℂ) := Complex.ext rfl (hz.2 k)
  simp only [normalizedCoordinateActions,WeightedCoeff.actionsFromNormalizedCoordinates_apply]
  conv_rhs => rw [hx,hy]
  simp only [baseActionWeight,ofReal_inv]
  push_cast
  have hn : (1+(actionIndexEquiv k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℝ)) ≠ 0)
  field_simp

/-- The actual weak inverse yields a normalized analytic pair chart at
EVERY real mean-zero rough source. Its real Arnold sequence is the literal
quadratic action map, on the full local real pair locus including zeros. -/
theorem exists_local_spectral_pair_chart
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q} ⊆ Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n) = hillHminusRealGapContourMoment q hr n 0)
    (q0 : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q0) (hm : q0.val 0 = 0) :
    ∃ z0 : Coeff 2 × Coeff 2, z0 ∈ Coeff.realPairLocus 2 ∧
      normalizedCoordinateActions z0 = I q0 ∧
      ∃ U : Set (Coeff 2 × Coeff 2), IsOpen U ∧ z0 ∈ U ∧
      ∃ Q : (Coeff 2 × Coeff 2) → PeriodOneHminusOne,
        AnalyticOnNhd ℂ Q U ∧ Q z0 = q0 ∧ ∀ z ∈ U,
          (Q z).val 0 = 0 ∧ (z ∈ Coeff.realPairLocus 2 →
            ∃ _hrz : IsRealPeriodOneHminusOne (Q z), I (Q z) = normalizedCoordinateActions z) := by
  obtain ⟨z0,hz0,U,hU,hzU,Q,hQ,hQ0,hd⟩ := exists_hillRough_pair_inverse D actionIndexEquiv q0 hr hm
  have hact (z : Coeff 2 × Coeff 2) (hz : z ∈ U) (hzr : z ∈ Coeff.realPairLocus 2) :
      I (Q z) = normalizedCoordinateActions z :=
    Arnold_action_of_pair_inverse_identity D Ω hΩ I hI hrec (Q z) ((hd z hz).2.2 hzr)
      z hzr (hd z hz).2.1
  refine ⟨z0,hz0,?_,U,hU,hzU,Q,hQ,hQ0,?_⟩
  · have hh := hact z0 hzU hz0
    rw [hQ0] at hh
    exact hh.symm
  · intro z hz
    exact ⟨(hd z hz).1,fun hzr => ⟨(hd z hz).2.2 hzr,hact z hz hzr⟩⟩

end NLS.Articles.KdVConvexity
