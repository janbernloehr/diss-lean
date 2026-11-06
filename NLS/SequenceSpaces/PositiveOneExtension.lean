import NLS.SequenceSpaces.PositiveOneReindex
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Bounded positive-index extension and restriction in the original l1 norm -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS

def positiveOneExtendFunction (e : ℤ ≃ ℕ+) (a : Coeff 1) (j : ℤ) : ℂ :=
  if hj : 0 < j then a (e.symm ⟨j.toNat,by omega⟩) else 0

theorem positiveOneExtendFunction_index (e : ℤ ≃ ℕ+) (a : Coeff 1) (k : ℤ) :
    positiveOneExtendFunction e a (positiveIndexInjection e k) = a k := by
  have hp : (0 : ℤ) < positiveIndexInjection e k := by
    dsimp only [positiveIndexInjection]
    exact_mod_cast (e k).pos
  rw [positiveOneExtendFunction, dif_pos hp]
  have he : (⟨(positiveIndexInjection e k).toNat,by omega⟩ : ℕ+) = e k := by
    apply Subtype.ext
    change ((e k : ℕ) : ℤ).toNat = (e k : ℕ)
    exact Int.toNat_natCast _
  rw [he,Equiv.symm_apply_apply]

theorem positiveOneExtendFunction_zero_outside (e : ℤ ≃ ℕ+) (a : Coeff 1)
    (j : ℤ) (hj : j ∉ range (positiveIndexInjection e)) : positiveOneExtendFunction e a j = 0 := by
  rw [positiveOneExtendFunction,dif_neg]
  intro hp
  apply hj
  refine ⟨e.symm ⟨j.toNat,by omega⟩,?_⟩
  change ((e (e.symm ⟨j.toNat,by omega⟩) : ℕ) : ℤ) = j
  have he := e.apply_symm_apply (⟨j.toNat,by omega⟩ : ℕ+)
  exact (congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ)) he).trans (Int.toNat_of_nonneg hp.le)

def positiveOneExtendCoeff (e : ℤ ≃ ℕ+) (a : Coeff 1) : Coeff 1 :=
  ⟨positiveOneExtendFunction e a,by
    apply memℓp_gen
    have hs := (lp.memℓp a).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    apply ((positiveIndexInjection_injective e).summable_iff (fun j hj => by
      rw [positiveOneExtendFunction_zero_outside e a j hj]
      simp)).mp
    simpa only [Function.comp_def,positiveOneExtendFunction_index] using hs⟩

theorem norm_positiveOneExtendCoeff (e : ℤ ≃ ℕ+) (a : Coeff 1) :
    ‖positiveOneExtendCoeff e a‖ = ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  congr 1
  have he := (positiveIndexInjection_injective e).tsum_eq
    (f := fun j => ‖positiveOneExtendFunction e a j‖^(1 : ℝ≥0∞).toReal) (by
      intro j hj
      by_contra h
      apply hj
      change ‖positiveOneExtendFunction e a j‖^(1 : ℝ≥0∞).toReal = 0
      rw [positiveOneExtendFunction_zero_outside e a j h]
      norm_num)
  simpa only [positiveOneExtendCoeff,positiveOneExtendFunction_index] using he.symm

def positiveOneExtendIsometry (e : ℤ ≃ ℕ+) : Coeff 1 →ₗᵢ[ℂ] Coeff 1 where
  toFun := positiveOneExtendCoeff e
  map_add' a b := by
    ext j
    change positiveOneExtendFunction e (a+b) j =
      positiveOneExtendFunction e a j+positiveOneExtendFunction e b j
    unfold positiveOneExtendFunction
    split_ifs <;> simp
  map_smul' c a := by
    ext j
    change positiveOneExtendFunction e (c • a) j = c*positiveOneExtendFunction e a j
    unfold positiveOneExtendFunction
    split_ifs <;> simp
  norm_map' := norm_positiveOneExtendCoeff e


end NLS
