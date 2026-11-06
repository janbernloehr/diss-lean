import NLS.SequenceSpaces.Reflection
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Bounded positive-index extension and restriction in the original Hilbert norm -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS

def positiveIndexInjection (e : ℤ ≃ ℕ+) (k : ℤ) : ℤ := ((e k : ℕ) : ℤ)

theorem positiveIndexInjection_injective (e : ℤ ≃ ℕ+) :
    Function.Injective (positiveIndexInjection e) := by
  intro j k h
  apply e.injective
  apply Subtype.ext
  exact Int.ofNat.inj h

def positiveReindexFunction (e : ℤ ≃ ℕ+) (a : Coeff 2) (j : ℤ) : ℂ :=
  if hj : 0 < j then a (e.symm ⟨j.toNat,by omega⟩) else 0

theorem positiveReindexFunction_index (e : ℤ ≃ ℕ+) (a : Coeff 2) (k : ℤ) :
    positiveReindexFunction e a (positiveIndexInjection e k) = a k := by
  have hp : (0 : ℤ) < positiveIndexInjection e k := by
    dsimp only [positiveIndexInjection]
    exact_mod_cast (e k).pos
  rw [positiveReindexFunction, dif_pos hp]
  have he : (⟨(positiveIndexInjection e k).toNat,by omega⟩ : ℕ+) = e k := by
    apply Subtype.ext
    change ((e k : ℕ) : ℤ).toNat = (e k : ℕ)
    exact Int.toNat_natCast _
  rw [he,Equiv.symm_apply_apply]

theorem positiveReindexFunction_zero_outside (e : ℤ ≃ ℕ+) (a : Coeff 2)
    (j : ℤ) (hj : j ∉ range (positiveIndexInjection e)) : positiveReindexFunction e a j = 0 := by
  rw [positiveReindexFunction,dif_neg]
  intro hp
  apply hj
  refine ⟨e.symm ⟨j.toNat,by omega⟩,?_⟩
  change ((e (e.symm ⟨j.toNat,by omega⟩) : ℕ) : ℤ) = j
  have he := e.apply_symm_apply (⟨j.toNat,by omega⟩ : ℕ+)
  exact (congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ)) he).trans (Int.toNat_of_nonneg hp.le)

def positiveReindexCoeff (e : ℤ ≃ ℕ+) (a : Coeff 2) : Coeff 2 :=
  ⟨positiveReindexFunction e a,by
    apply memℓp_gen
    have hs := (lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    apply ((positiveIndexInjection_injective e).summable_iff (fun j hj => by
      rw [positiveReindexFunction_zero_outside e a j hj]
      simp)).mp
    simpa only [Function.comp_def,positiveReindexFunction_index] using hs⟩

theorem norm_positiveReindexCoeff (e : ℤ ≃ ℕ+) (a : Coeff 2) :
    ‖positiveReindexCoeff e a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  have he := (positiveIndexInjection_injective e).tsum_eq
    (f := fun j => ‖positiveReindexFunction e a j‖^(2 : ℝ≥0∞).toReal) (by
      intro j hj
      by_contra h
      apply hj
      change ‖positiveReindexFunction e a j‖^(2 : ℝ≥0∞).toReal = 0
      rw [positiveReindexFunction_zero_outside e a j h]
      norm_num)
  simpa only [positiveReindexCoeff,positiveReindexFunction_index] using he.symm

def positiveReindexIsometry (e : ℤ ≃ ℕ+) : Coeff 2 →ₗᵢ[ℂ] Coeff 2 where
  toFun := positiveReindexCoeff e
  map_add' a b := by
    ext j
    change positiveReindexFunction e (a+b) j =
      positiveReindexFunction e a j+positiveReindexFunction e b j
    unfold positiveReindexFunction
    split_ifs <;> simp
  map_smul' c a := by
    ext j
    change positiveReindexFunction e (c • a) j = c*positiveReindexFunction e a j
    unfold positiveReindexFunction
    split_ifs <;> simp
  norm_map' := norm_positiveReindexCoeff e

def positiveReindexPull (e : ℤ ≃ ℕ+) (a : Coeff 2) : Coeff 2 :=
  ⟨fun k => a (positiveIndexInjection e k),memℓp_gen
    (((lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).comp_injective
      (positiveIndexInjection_injective e))⟩

theorem norm_positiveReindexPull_le (e : ℤ ≃ ℕ+) (a : Coeff 2) :
    ‖positiveReindexPull e a‖ ≤ ‖a‖ := by
  have hsum := tsum_comp_le_tsum_of_inj
    ((lp.memℓp a).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _) (positiveIndexInjection_injective e)
  have hleft := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (positiveReindexPull e a)
  have hright := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
  have hs' : ‖positiveReindexPull e a‖^(2 : ℝ≥0∞).toReal ≤ ‖a‖^(2 : ℝ≥0∞).toReal := by
    rw [hleft,hright]
    exact hsum
  have hs : ‖positiveReindexPull e a‖^2 ≤ ‖a‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hs'
  nlinarith [norm_nonneg (positiveReindexPull e a),norm_nonneg a]

def positiveReindexPullCLM (e : ℤ ≃ ℕ+) : Coeff 2 →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := positiveReindexPull e
      map_add' := by intro a b; ext k; rfl
      map_smul' := by intro c a; ext k; rfl }
    1 (by
      intro a
      change ‖positiveReindexPull e a‖ ≤ 1*‖a‖
      rw [one_mul]
      exact norm_positiveReindexPull_le e a)

end NLS
