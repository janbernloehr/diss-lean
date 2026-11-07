import NLS.Articles.KdVKdV2Frequencies.GlobalRoughActionIsospectral
import NLS.SequenceSpaces.SignedPairActionProducts
import NLS.Articles.KdVConvexity.AnalyticSeries

/-! Equal normalized native pair actions determine the same entire
actual Hill discriminant, with all raw Sobolev factors retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem discriminant_eq_of_weighted_pair_actions (D : GlobalRoughAbelianForwardData)
    (t : ℝ) (q p : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hqm : q.val 0=0) (hpm : p.val 0=0) (z w : Coeff 2 × Coeff 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=
      (signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (hj : ∀ j : ℤ, (D.signed p).val j=
      (signedPairToDeleted actionIndexEquiv w).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z) :
    hillHminusDiscriminant q=hillHminusDiscriminant p := by
  funext E
  apply D.discriminant_eq_of_signed_actions_eq q p hq hp hqm hpm _ E
  intro n
  have hprod (v : Coeff 2 × Coeff 2) :
      (signedPairToDeleted actionIndexEquiv v).val (n : ℤ)*
        (signedPairToDeleted actionIndexEquiv v).val (-(n : ℤ))=
          quadraticActionsExponent (q := 1) v (actionIndexEquiv.symm n) := by
    simpa only [positiveIndexInjection,Equiv.apply_symm_apply] using
      signedPairToDeleted_product actionIndexEquiv v (actionIndexEquiv.symm n)
  rw [hi (n : ℤ),hi (-(n : ℤ)),hj (n : ℤ),hj (-(n : ℤ)),div_mul_div_comm,
    div_mul_div_comm,hprod z,hprod w,ha]

end NLS.Articles.KdVKdV2Frequencies
