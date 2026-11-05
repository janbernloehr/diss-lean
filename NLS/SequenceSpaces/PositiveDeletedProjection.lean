import NLS.SequenceSpaces.Multiplier

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.Coeff



def positiveDeletedSymbol (n : ℤ) : Coeff ⊤ :=
  ⟨fun m => if 0 < m ∧ m ≠ n then 1 else 0,memℓp_infty ⟨1,by
    rintro _ ⟨m,rfl⟩
    change ‖(if 0 < m ∧ m ≠ n then (1 : ℂ) else 0)‖ ≤ (1 : ℝ)
    split_ifs <;> norm_num⟩⟩

def positiveDeletedProjection (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) : Coeff p →L[ℂ] Coeff p :=
  multiplierCLM (positiveDeletedSymbol n)

theorem positiveDeletedProjection_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (n m : ℤ) (a : Coeff p) :
    positiveDeletedProjection p n a m = if 0 < m ∧ m ≠ n then a m else 0 := by
  change (if 0 < m ∧ m ≠ n then (1 : ℂ) else 0)*a m = _
  split_ifs <;> simp only [one_mul,zero_mul]

theorem positiveDeletedProjection_eq_self_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : Coeff p) :
    positiveDeletedProjection p n a = a ↔ ∀ m : ℤ, m ≤ 0 ∨ m = n → a m = 0 := by
  constructor
  · intro h m hm
    have he := congrArg (fun b : Coeff p => b m) h
    rw [positiveDeletedProjection_apply,if_neg (by omega)] at he
    exact he.symm
  · intro h
    ext m
    rw [positiveDeletedProjection_apply]
    split_ifs with hm
    · rfl
    · exact (h m (by omega)).symm

theorem positiveDeletedProjection_idempotent (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) (a : Coeff p) :
    positiveDeletedProjection p n (positiveDeletedProjection p n a) = positiveDeletedProjection p n a := by
  ext m
  rw [positiveDeletedProjection_apply,positiveDeletedProjection_apply]
  split_ifs
  · rfl
  · rfl

end NLS.Coeff
