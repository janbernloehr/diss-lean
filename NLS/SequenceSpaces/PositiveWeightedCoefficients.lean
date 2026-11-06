import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.SequenceSpaces.Multiplier

/-! # Positive-frequency weighted coefficient Banach spaces

The positive-index target is a closed complex subspace of the actual
weighted sequence space. Its bounded projection keeps every positive raw
coefficient and sets only the nonpositive encoding slots to zero.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveSubmodule : Submodule ℂ (WeightedCoeff w p) where
  carrier := {a | ∀ n : ℤ, n ≤ 0 → a.val n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by intro a b ha hb n hn; simp only [add_val,ha n hn,hb n hn,add_zero]
  smul_mem' := by intro c a ha n hn; simp only [smul_val,ha n hn,mul_zero]

theorem isClosed_positiveSubmodule : IsClosed (positiveSubmodule w p : Set (WeightedCoeff w p)) := by
  have he : (positiveSubmodule w p : Set (WeightedCoeff w p)) =
      ⋂ n : ℤ, ⋂ (_ : n ≤ 0), {a | evalCLM w p n a = 0} := by
    ext a
    change (∀ n : ℤ, n ≤ 0 → a.val n = 0) ↔ a ∈ ⋂ n : ℤ, ⋂ (_ : n ≤ 0), {a | evalCLM w p n a = 0}
    simp only [mem_ofPred_eq,mem_iInter,evalCLM_apply]
  rw [he]
  exact isClosed_iInter (fun n => isClosed_iInter (fun _ => isClosed_eq (evalCLM w p n).continuous continuous_const))

instance positiveSubmoduleComplete : CompleteSpace (positiveSubmodule w p) :=
  (isClosed_positiveSubmodule w p).completeSpace_coe

private def positiveSymbol : Coeff ⊤ :=
  ⟨fun n => if 0 < n then 1 else 0,memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    change ‖(if 0 < n then (1 : ℂ) else 0)‖ ≤ 1
    split_ifs <;> norm_num⟩⟩

def positiveAmbientProjection : WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  (weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.multiplierCLM positiveSymbol).comp (weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem positiveAmbientProjection_apply (a : WeightedCoeff w p) (n : ℤ) :
    (positiveAmbientProjection w p a).val n = if 0 < n then a.val n else 0 := by
  change ((if 0 < n then 1 else 0)*((w n : ℂ)*a.val n))/(w n : ℂ) = _
  split_ifs <;> simp [w.complex_ne_zero n]

def positiveProjection : WeightedCoeff w p →L[ℂ] positiveSubmodule w p :=
  (positiveAmbientProjection w p).codRestrict (positiveSubmodule w p) (by
    intro a n hn
    simp only [positiveAmbientProjection_apply,if_neg (by omega : ¬0 < n)])

@[simp] theorem positiveProjection_apply (a : WeightedCoeff w p) (n : ℤ) :
    (positiveProjection w p a).val.val n = if 0 < n then a.val n else 0 :=
  positiveAmbientProjection_apply w p a n

theorem positiveProjection_eq_self (a : positiveSubmodule w p) : positiveProjection w p a.val = a := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  rw [positiveProjection_apply]
  split_ifs with hn
  · rfl
  · exact (a.property n (by omega)).symm

end NLS.WeightedCoeff
