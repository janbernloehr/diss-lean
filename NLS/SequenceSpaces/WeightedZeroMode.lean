import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.WeightedMultiplier

/-! The exact closed zero-mode kernel and a bounded projection onto it.
No mean coordinate remains in this Banach source or target. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def zeroModeSubmodule (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℂ (WeightedCoeff w p) :=
  (evalCLM w p 0).ker

theorem mem_zeroModeSubmodule (w : Weight) (a : WeightedCoeff w p) :
    a ∈ zeroModeSubmodule w p ↔ a.val 0=0 := Iff.rfl

instance zeroModeSubmodule_complete (w : Weight) : CompleteSpace (zeroModeSubmodule w p) :=
  (evalCLM w p 0).isClosed_ker.completeSpace_coe

def eraseZeroModeCLM (w : Weight) : WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  weightedMultiplierCLM w w (fun k => if k=0 then 0 else 1) 1 zero_le_one (by
    intro k
    by_cases hk : k=0
    · simp only [if_pos hk,norm_zero,mul_zero,one_mul]
      exact (w.positive k).le
    · simp only [if_neg hk,norm_one,mul_one,one_mul]
      exact le_rfl)

theorem eraseZeroModeCLM_apply (w : Weight) (a : WeightedCoeff w p) (k : ℤ) :
    (eraseZeroModeCLM w a).val k=if k=0 then 0 else a.val k := by
  change (if k=0 then (0:ℂ) else 1)*a.val k=_
  split_ifs <;> simp only [one_mul,zero_mul]

def zeroModeProjection (w : Weight) : WeightedCoeff w p →L[ℂ] zeroModeSubmodule w p :=
  (eraseZeroModeCLM w).codRestrict (zeroModeSubmodule w p) (by
    intro a
    change (eraseZeroModeCLM w a).val 0=0
    rw [eraseZeroModeCLM_apply,if_pos rfl])

theorem zeroModeProjection_coe (w : Weight) (a : WeightedCoeff w p) (ha : a.val 0=0) :
    (zeroModeProjection w a : WeightedCoeff w p)=a := by
  apply Subtype.ext
  funext k
  change (eraseZeroModeCLM w a).val k=a.val k
  rw [eraseZeroModeCLM_apply]
  split_ifs with hk
  · subst k
    exact ha.symm
  · rfl

end NLS.WeightedCoeff
