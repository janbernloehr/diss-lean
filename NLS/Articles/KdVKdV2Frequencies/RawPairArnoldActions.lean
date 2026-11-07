import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianRegularity
import NLS.Articles.KdVConvexity.GlobalArnoldCalibration
import NLS.SequenceSpaces.SignedHilbertPairs
import NLS.SequenceSpaces.SobolevHomogeneous

/-! Original RAW actions of unweighted signed Hilbert pair coordinates.
The physical squared signed coefficient is exactly the original action;
there is no residual weak-action weight at the H^(-1/2) threshold. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem raw_signed_action_norm (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) :
    (1+(n : ℝ))*‖D.positive q (n : ℤ)‖^2=‖(D.signed q).val (n : ℤ)‖^2 := by
  have hp : (Weight.sobolev (-1/2) (n : ℤ) : ℂ)*(D.signed q).val (n : ℤ)=D.positive q (n : ℤ) := by
    rw [D.signed_positive_real q hr _ (by exact_mod_cast n.pos)]
    exact mul_div_cancel₀ _ (Weight.complex_ne_zero _ _)
  rw [←hp,Weight.norm_sobolev_mul_sq]
  norm_num only [show 2*(-1/2 : ℝ)=-1 by norm_num,Real.rpow_neg_one,
    Int.cast_natCast,Nat.cast_ofNat]
  rw [abs_of_pos (by exact_mod_cast n.pos : (0 : ℝ)<n)]
  have hn : 1+(n : ℝ)≠0 := by positivity
  field_simp

theorem Arnold_action_of_raw_pair_inverse_identity
    (D : GlobalRoughAbelianForwardData)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (I : PeriodOneHminusOne → BaseActionSpace) (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : Coeff 2 × Coeff 2) (hz : z∈Coeff.realPairLocus 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted actionIndexEquiv z).val j) (k : ℤ) :
    (I q).val k=quadraticActionsExponent (q := 1) z k := by
  have hc := global_Arnold_positive_calibration D Ω hΩ I hI hrec q hr (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply] at hc
  have hn := norm_signedPairToDeleted_positive_sq actionIndexEquiv z hz k
  change ‖(signedPairToDeleted actionIndexEquiv z).val (actionIndexEquiv k : ℤ)‖^2=_ at hn
  rw [raw_signed_action_norm D q hr,hi,hn] at hc
  rw [hc,quadraticActionsExponent_apply]
  have hx : z.1 k=((z.1 k).re : ℂ) := Complex.ext rfl (hz.1 k)
  have hy : z.2 k=((z.2 k).re : ℂ) := Complex.ext rfl (hz.2 k)
  conv_rhs => rw [hx,hy]
  push_cast
  ring

end NLS.Articles.KdVKdV2Frequencies
