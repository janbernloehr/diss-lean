import NLS.SequenceSpaces.ShiftedHolderDecay

/-! Uniform decay of arbitrary families dominated by two opposite
translated Holder pairings. The decaying bound precedes the family index. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem exists_uniform_two_shift_holder_decay
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hc : p.toReal.HolderConjugate q.toReal)
    (a : Coeff p) (b : Coeff q) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℤ → ℝ, (∀ n, 0 ≤ B n) ∧ Tendsto B cofinite (𝓝 0) ∧
      ∀ u : ℤ → ℂ, ∀ n : ℤ,
        (∀ m, ‖u m‖ ≤ C*‖a m‖*(‖shift n b m‖+‖shift (-n) b m‖)) →
        Summable (fun m => ‖u m‖) ∧ ‖∑' m, u m‖ ≤ B n := by
  let S : ℤ → ℝ := fun n => ∑' m : ℤ, ‖a m‖*‖shift n b m‖
  let B : ℤ → ℝ := fun n => C*(S n+S (-n))
  have hS : Tendsto S cofinite (𝓝 0) := tendsto_tsum_norm_mul_shift_zero hp hq hc a b
  have hneg : Tendsto (fun n : ℤ => -n) cofinite cofinite :=
    (Equiv.neg ℤ).injective.tendsto_cofinite
  have hB : Tendsto B cofinite (𝓝 0) := by
    simpa only [B,Function.comp_apply,add_zero,mul_zero] using tendsto_const_nhds.mul (hS.add (hS.comp hneg))
  refine ⟨B,fun n => mul_nonneg hC (add_nonneg
    (tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))),hB,?_⟩
  intro u n hu
  have hplus := (lp.tsum_mul_le_mul_norm hc a (shift n b)).1
  have hminus := (lp.tsum_mul_le_mul_norm hc a (shift (-n) b)).1
  have hmajor : Summable (fun m : ℤ => C*(‖a m‖*‖shift n b m‖+‖a m‖*‖shift (-n) b m‖)) :=
    (hplus.add hminus).mul_left C
  have hbound (m : ℤ) : ‖u m‖ ≤ C*(‖a m‖*‖shift n b m‖+‖a m‖*‖shift (-n) b m‖) := by
    convert hu m using 1
    ring
  have hs : Summable (fun m => ‖u m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmajor
  refine ⟨hs,(norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' m : ℤ, C*(‖a m‖*‖shift n b m‖+‖a m‖*‖shift (-n) b m‖) :=
      hs.tsum_le_tsum hbound hmajor
    _ = B n := by rw [tsum_mul_left,hplus.tsum_add hminus]

end NLS.Coeff
