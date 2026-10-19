import NLS.SequenceSpaces.CoefficientCompactness
import NLS.SequenceSpaces.Weighted

/-! # Bounded weighted limits from coordinatewise convergence

Uniformly bounded weighted sequences retain their weight and norm bound under coefficientwise limits.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- Uniformly bounded weighted sequences retain their weight and the same
norm bound under coefficientwise convergence. No uniform tail bound is
required. -/
theorem exists_of_bounded_coefficientwise_tendsto
    {α : Type*} {l : Filter α} [NeBot l] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : Weight) (a : α → WeightedCoeff w p) (f : ℤ → ℂ)
    (C : ℝ) (hb : ∀ i, ‖a i‖ ≤ C)
    (ht : ∀ n, Tendsto (fun i => (a i).val n) l (𝓝 (f n))) :
    ∃ b : WeightedCoeff w p, (∀ n, b.val n = f n) ∧ ‖b‖ ≤ C := by
  let A (i : α) : Coeff p := weightEquiv w p (a i)
  have hA (i : α) : ‖A i‖ ≤ C := by simpa only [A,← norm_eq] using hb i
  have hbounded : Bornology.IsBounded (range A) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨C,by rintro _ ⟨i,rfl⟩; exact hA i⟩
  have hlim : Tendsto (fun i n => A i n) l (𝓝 (fun n => (w n:ℂ)*f n)) := by
    rw [tendsto_pi_nhds]
    intro n
    exact tendsto_const_nhds.mul (ht n)
  have hmem := lp.memℓp_of_tendsto hbounded hlim
  let b : WeightedCoeff w p := ⟨f,hmem⟩
  refine ⟨b,fun _ => rfl,?_⟩
  exact lp.norm_le_of_tendsto (Eventually.of_forall hA) hlim

end NLS.WeightedCoeff
