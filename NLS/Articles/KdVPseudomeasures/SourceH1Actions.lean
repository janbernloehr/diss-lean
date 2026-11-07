import NLS.Articles.KdVPseudomeasures.SourceHamiltonianActionDescent
import NLS.SequenceSpaces.PositiveCartesianParameters
import NLS.SequenceSpaces.Reflection

/-! The literal positive n^3-weighted l1 action space and its bounded
normalization into the ordinary l1 cone used by analytic descent. -/
noncomputable section
open Set Complex NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

abbrev SourceH1Actions := positiveSubmodule (Weight.positiveSobolev 3) 1

def sourceH1NormalizedActions : SourceH1Actions →L[ℂ] Coeff 1 :=
  positiveToCoeff (Weight.positiveSobolev 3) 1+
    Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (positiveToCoeff (Weight.positiveSobolev 3) 1)

theorem sourceH1NormalizedActions_apply (a : SourceH1Actions) (k : ℤ) :
    sourceH1NormalizedActions a k =
      (Weight.positiveSobolev 3 k:ℂ)*a.val.val k+
        (Weight.positiveSobolev 3 (-k):ℂ)*a.val.val (-k) := rfl

theorem sourceH1NormalizedActions_positive (a : SourceH1Actions) (k : ℤ) (hk : 0 < k) :
    sourceH1NormalizedActions a k=(Weight.positiveSobolev 3 k:ℂ)*a.val.val k := by
  rw [sourceH1NormalizedActions_apply,a.property (-k) (by omega),mul_zero,add_zero]

theorem sourceH1NormalizedActions_neg (a : SourceH1Actions) (k : ℤ) :
    sourceH1NormalizedActions a (-k)=sourceH1NormalizedActions a k := by
  rw [sourceH1NormalizedActions_apply,sourceH1NormalizedActions_apply,neg_neg,add_comm]

theorem sourceH1NormalizedActions_zero (a : SourceH1Actions) : sourceH1NormalizedActions a 0=0 := by
  rw [sourceH1NormalizedActions_apply,neg_zero,a.property 0 le_rfl,mul_zero,zero_add]

theorem sourceH1_action_weight_square (k : ℤ) (hk : 0 < k) :
    (Weight.signedSobolev (signedStepOrder (1/2) 1) k)^2=Weight.positiveSobolev 3 k := by
  rw [Weight.signedSobolev_positive _ k hk]
  simp only [Weight.positiveSobolev,hk,if_pos]
  rw [← Real.rpow_natCast,← Real.rpow_mul (by exact_mod_cast hk.le : (0:ℝ)≤k)]
  congr 1
  norm_num [signedStepOrder]

def sourceH1CanonicalActions (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : SourceH1Actions :=
  positiveFromCoeff (Weight.positiveSobolev 3) 1
    (quadraticActionsExponent
      (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
        (signedRealCartesianParameters (signedStepOrder (1/2) 1) z)))

/-- Every coordinate is the original canonical action z_n*z_-n,
without changing the n^3 action weight. -/
theorem sourceH1CanonicalActions_apply (z : RealSignedHilbert (signedStepOrder (1/2) 1))
    (k : ℤ) (hk : 0 < k) :
    (sourceH1CanonicalActions z).val.val k=z.val.val.val k*z.val.val.val (-k) := by
  rw [sourceH1CanonicalActions,positiveFromCoeff_apply,if_pos hk,signedRealCartesianParameters_actions]
  rw [← sourceH1_action_weight_square k hk,ofReal_pow]
  convert mul_div_cancel_left₀ (z.val.val.val k*z.val.val.val (-k))
    (pow_ne_zero 2 ((Weight.signedSobolev (signedStepOrder (1/2) 1)).complex_ne_zero k)) using 1
  ring

theorem sourceH1CanonicalActions_normalized (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    sourceH1NormalizedActions (sourceH1CanonicalActions z) =
      quadraticActionsExponent
        (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
          (signedRealCartesianParameters (signedStepOrder (1/2) 1) z)) := by
  ext k
  have hpos (j : ℤ) (hj : 0 < j) :
      sourceH1NormalizedActions (sourceH1CanonicalActions z) j =
        quadraticActionsExponent (q := 1)
          (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
            (signedRealCartesianParameters (signedStepOrder (1/2) 1) z)) j := by
    rw [sourceH1NormalizedActions_positive _ j hj,sourceH1CanonicalActions_apply _ j hj,
      signedRealCartesianParameters_actions,← sourceH1_action_weight_square j hj,ofReal_pow]
    ring
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [← neg_neg k,sourceH1NormalizedActions_neg,hpos (-k) (by omega),
      signedRealCartesianParameters_actions,signedRealCartesianParameters_actions,
      Weight.signedSobolev_neg,neg_neg]
    ring
  · subst k
    have hz0 : z.val.val.val 0=0 := z.val.property
    rw [sourceH1NormalizedActions_zero,signedRealCartesianParameters_actions,hz0,mul_zero,zero_mul]
  · exact hpos k hk

theorem sourceH1NormalizedActions_nonnegative (a : SourceH1Actions)
    (ha : ∀ k, (a.val.val k).im=0 ∧ 0≤(a.val.val k).re) :
    sourceH1NormalizedActions a ∈ Coeff.nonnegativeLocus 1 := by
  intro k
  rw [sourceH1NormalizedActions_apply]
  simp only [add_im,add_re,mul_im,mul_re,ofReal_re,ofReal_im,(ha k).1,(ha (-k)).1,
    zero_mul,mul_zero,add_zero,sub_zero]
  exact ⟨trivial,add_nonneg
    (mul_nonneg ((Weight.positiveSobolev 3).positive k).le (ha k).2)
    (mul_nonneg ((Weight.positiveSobolev 3).positive (-k)).le (ha (-k)).2)⟩

end NLS.Articles.KdVPseudomeasures
