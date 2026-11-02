import NLS.Articles.KdVConvexity.AnalyticSeries
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.WeightedNonnegativeActions

/-! # The positive ell2 action space inside the weighted base action space

The action weight is exactly <n>^-1 = (1+n)^-1, with n >= 1.
The integer bijection only enumerates positive action indices. Raw action
coordinates are preserved by the continuous inclusion into ell^(-1,1).
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

/-- Positive-index Hilbert actions, reindexed without changing their norm. -/
def actionReindex : ActionSpace →ₗᵢ[ℂ] Coeff 2 where
  toFun a := ⟨fun k => a (actionIndexEquiv k), by
    apply memℓp_gen
    exact actionIndexEquiv.summable_iff.mpr
      ((lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' a := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact actionIndexEquiv.tsum_eq (fun n => ‖a n‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] theorem actionReindex_apply (a : ActionSpace) (k : ℤ) :
    actionReindex a k = a (actionIndexEquiv k) := rfl

/-- The actual negative-order weight of the paper's base action space. -/
def baseActionWeight : Weight :=
  ⟨fun k => (1 + (actionIndexEquiv k : ℝ))⁻¹, fun _ => by positivity⟩

/-- Weighted ell^(-1,1), retaining raw action coefficients. -/
abbrev BaseActionSpace := WeightedCoeff baseActionWeight 1

/-- The reciprocal weight is square summable, by the convergent p-series. -/
theorem memlp_baseActionWeight : Memℓp (fun k : ℤ => (baseActionWeight k : ℂ)) 2 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hi : Function.Injective (fun n : ℕ+ => (n : ℕ) + 1) := by
    intro n m h
    apply Subtype.ext
    change (n : ℕ) + 1 = (m : ℕ) + 1 at h
    exact Nat.add_right_cancel h
  have hp := hs.comp_injective hi
  apply memℓp_gen
  have hp' := actionIndexEquiv.summable_iff.mpr hp
  apply hp'.congr
  intro k
  simp only [Function.comp_def, baseActionWeight, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ (1 + (actionIndexEquiv k : ℝ))⁻¹),
    ENNReal.toReal_ofNat, Real.rpow_two, inv_pow]
  push_cast
  simp only [add_comm, one_div]

/-- The continuous inclusion ell2 -> ell^(-1,1), with raw coordinates intact. -/
def baseActionInclusion : ActionSpace →L[ℂ] BaseActionSpace :=
  (WeightedCoeff.weightIsometry baseActionWeight 1).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((Coeff.holderProduct (p := 2) (r := 2) (q := 1))
      ⟨fun k => (baseActionWeight k : ℂ), memlp_baseActionWeight⟩).comp
        actionReindex.toContinuousLinearMap)

/-- No extra normalization is applied to the physical actions by this inclusion. -/
@[simp] theorem baseActionInclusion_apply (a : ActionSpace) (k : ℤ) :
    (baseActionInclusion a).val k = a (actionIndexEquiv k) := by
  change (baseActionWeight k : ℂ) * a (actionIndexEquiv k) / (baseActionWeight k : ℂ) = _
  exact mul_div_cancel_left₀ _ (baseActionWeight.complex_ne_zero k)

/-- The base inclusion retains distinct raw positive-index action sequences. -/
theorem baseActionInclusion_injective : Function.Injective baseActionInclusion := by
  intro a b hab
  ext n
  have hk := congrArg (fun c : BaseActionSpace => c.val (actionIndexEquiv.symm n)) hab
  simpa only [baseActionInclusion_apply, Equiv.apply_symm_apply] using hk

/-- The source's weighted ell^(-1,1) norm is exactly the weighted sum of
positive-index raw action values, with <n> = 1+n. -/
theorem norm_baseActionInclusion (a : ActionSpace) :
    ‖baseActionInclusion a‖ = ∑' n : ℕ+, ‖a n‖ / (1 + (n : ℝ)) := by
  change ‖WeightedCoeff.weightEquiv baseActionWeight 1 (baseActionInclusion a)‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, one_div_one, Real.rpow_one,
    WeightedCoeff.weightEquiv_apply, baseActionInclusion_apply, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (baseActionWeight.positive _).le]
  simp only [baseActionWeight, div_eq_mul_inv, mul_comm]
  exact actionIndexEquiv.tsum_eq (fun n => (1 + (n : ℝ))⁻¹ * ‖a n‖)

/-- The inclusion preserves the entire nonnegative cone, including its boundary. -/
theorem baseActionInclusion_mem_nonnegative (a : ActionSpace) (ha : a ∈ positiveQuadrant) :
    baseActionInclusion a ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1 := by
  intro k
  simpa only [baseActionInclusion_apply] using ha (actionIndexEquiv k)

/-- An open neighborhood of all nonnegative base actions pulls back to a complex
open neighborhood of every positive ell2 action, rather than only of zero. -/
theorem preimage_base_neighborhood (U : Set BaseActionSpace) (hU : IsOpen U)
    (hcone : WeightedCoeff.nonnegativeLocus baseActionWeight 1 ⊆ U) :
    IsOpen (baseActionInclusion ⁻¹' U) ∧ positiveQuadrant ⊆ baseActionInclusion ⁻¹' U := by
  exact ⟨hU.preimage baseActionInclusion.continuous,
    fun a ha => hcone (baseActionInclusion_mem_nonnegative a ha)⟩

end NLS.Articles.KdVConvexity
