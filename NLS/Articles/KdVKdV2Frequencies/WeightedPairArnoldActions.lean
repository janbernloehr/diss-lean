import NLS.Articles.KdVKdV2Frequencies.RawPairArnoldActions

/-! Exact original Arnold actions of normalized native Sobolev pairs.
The action weight is twice the signed coordinate weight, at the original
positive frequency label. No enumeration weight replaces this label. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem sobolev_pair_weight_square (t : ℝ) (j : ℤ) :
    Weight.sobolev (2*t-1) j=(Weight.sobolev (t-1/2) j)^2 := by
  simp only [Weight.sobolev_apply]
  rw [←Real.rpow_two,←Real.rpow_mul (by positivity : (0 : ℝ)≤1+|(j : ℝ)|)]
  congr 1
  ring

theorem Arnold_action_of_weighted_pair_inverse_identity
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (t : ℝ) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=
      (signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ)) (k : ℤ) :
    (Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)*(I q).val k=
      quadraticActionsExponent (q := 1) z k := by
  have hc := global_Arnold_positive_calibration D Ω hΩ I hI hrec q hr (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply] at hc
  have hn := norm_signedPairToDeleted_positive_sq actionIndexEquiv z hz k
  change ‖(signedPairToDeleted actionIndexEquiv z).val (actionIndexEquiv k : ℤ)‖^2=_ at hn
  rw [raw_signed_action_norm D q hr,hi,norm_div,div_pow,Complex.norm_real,
    Real.norm_of_nonneg ((Weight.sobolev (t-1/2)).positive _).le,hn] at hc
  rw [hc,quadraticActionsExponent_apply,sobolev_pair_weight_square]
  have hx : z.1 k=((z.1 k).re : ℂ) := Complex.ext rfl (hz.1 k)
  have hy : z.2 k=((z.2 k).re : ℂ) := Complex.ext rfl (hz.2 k)
  rw [hx,hy]
  simp only [Complex.ofReal_re]
  push_cast
  have hw := Weight.complex_ne_zero (Weight.sobolev (t-1/2)) (actionIndexEquiv k : ℤ)
  field_simp [hw]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)

end NLS.Articles.KdVKdV2Frequencies
