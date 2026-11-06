import NLS.Articles.KdVConvexity.OriginalActionDomainRealization
import NLS.SequenceSpaces.WeightedMultiplier

/-! # The original ell^(3,1) action Banach space inside ell2, with unchanged raw coordinates -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def originalActionWeight : Weight :=
  ⟨fun k => (1+(actionIndexEquiv k : ℝ))^3,fun k => by positivity⟩

abbrev OriginalActionSpace := WeightedCoeff originalActionWeight 1

def originalActionToCoeffOne : OriginalActionSpace →L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry Weight.one 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.inclusionCLM originalActionWeight Weight.one (fun k => by
      change 1 ≤ (1+(actionIndexEquiv k : ℝ))^3
      exact one_le_pow₀ (by
        have hn : 0 ≤ (actionIndexEquiv k : ℝ) := by positivity
        linarith)))

@[simp] theorem originalActionToCoeffOne_apply (b : OriginalActionSpace) (k : ℤ) :
    originalActionToCoeffOne b k=b.val k := by
  change (Weight.one k : ℂ)*(WeightedCoeff.inclusionCLM originalActionWeight Weight.one _ b).val k=b.val k
  rw [WeightedCoeff.inclusionCLM_apply]
  simp only [Weight.one_apply,ofReal_one,one_mul]

/-- The original complex weighted ell^(3,1) space embeds continuously into
the positive-index Hilbert action space without changing any action. -/
def originalActionInclusion : OriginalActionSpace →L[ℂ] ActionSpace :=
  actionUnreindex.toContinuousLinearMap.comp
    ((Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)).comp originalActionToCoeffOne)

@[simp] theorem originalActionInclusion_apply (b : OriginalActionSpace) (n : ℕ+) :
    originalActionInclusion b n=b.val (actionIndexEquiv.symm n) := by
  change actionUnreindex (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (originalActionToCoeffOne b)) n=_
  rw [actionUnreindex_apply,Coeff.exponentInclusion_apply,originalActionToCoeffOne_apply]

theorem originalActionInclusion_mem_domain (b : OriginalActionSpace)
    (hb : b ∈ WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    originalActionInclusion b ∈ originalPositiveActionDomain := by
  refine ⟨?_,?_⟩
  · intro n
    simpa only [originalActionInclusion_apply] using hb (actionIndexEquiv.symm n)
  · have hs := (lp.memℓp (WeightedCoeff.weightEquiv originalActionWeight 1 b)).summable
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    have hsn : Summable (fun k : ℤ => (1+(actionIndexEquiv k : ℝ))^3*‖b.val k‖) := by
      simp only [ENNReal.toReal_one,Real.rpow_one] at hs
      apply hs.congr
      intro k
      change ‖(originalActionWeight k : ℂ)*b.val k‖=(1+(actionIndexEquiv k : ℝ))^3*‖b.val k‖
      rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos (originalActionWeight.positive k)]
      rfl
    have hpos := actionIndexEquiv.symm.summable_iff.mpr hsn
    simpa only [Function.comp_def,Equiv.apply_symm_apply,originalActionInclusion_apply] using hpos

theorem original_domain_has_weighted_representative
    (a : ActionSpace) (ha : a ∈ originalPositiveActionDomain) :
    ∃ b : OriginalActionSpace, b ∈ WeightedCoeff.nonnegativeLocus originalActionWeight 1 ∧
      originalActionInclusion b=a := by
  have hb : Memℓp (fun k => (originalActionWeight k : ℂ)*a (actionIndexEquiv k)) 1 := by
    apply memℓp_gen
    have hs := actionIndexEquiv.summable_iff.mpr ha.2
    have hs' : Summable (fun k : ℤ => (1+(actionIndexEquiv k : ℝ))^3*‖a (actionIndexEquiv k)‖) := by
      simpa only [Function.comp_def] using hs
    apply hs'.congr
    intro k
    simp only [ENNReal.toReal_one,Real.rpow_one,norm_mul,norm_real,Real.norm_eq_abs,
      abs_of_pos (originalActionWeight.positive k)]
    rfl
  let b : OriginalActionSpace := ⟨fun k => a (actionIndexEquiv k),hb⟩
  refine ⟨b,(fun k => ha.1 (actionIndexEquiv k)),?_⟩
  ext n
  exact (originalActionInclusion_apply b n).trans
    (congrArg (fun m : ℕ+ => a m) (actionIndexEquiv.apply_symm_apply n))

end NLS.Articles.KdVConvexity
