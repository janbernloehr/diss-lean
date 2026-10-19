import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Finite raw-coordinate blocks in weighted spaces

Finite blocks retain their raw coefficients and depend continuously on them in the actual weighted norm.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Insert finitely many raw coefficients in the actual weighted space. -/
def finiteBlock (w : Weight) (S : Finset ℤ) (f : ℤ → ℂ) : WeightedCoeff w p :=
  ∑ n ∈ S, f n • single (p := p) w n 1

@[simp] theorem finiteBlock_val (w : Weight) (S : Finset ℤ) (f : ℤ → ℂ) (n : ℤ) :
    (finiteBlock (p := p) w S f).val n = if n ∈ S then f n else 0 := by
  classical
  change evalCLM w p n (∑ j ∈ S, f j • single w j 1) = _
  rw [map_sum]
  have he : (∑ j ∈ S, evalCLM w p n (f j • single w j 1)) =
      ∑ j ∈ S, if j = n then f n else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = n
    · subst j
      simp
    · simp [hj,Ne.symm hj]
  rw [he]
  simp

/-- A finite weighted block depends continuously on its raw coordinates. -/
theorem continuousAt_finiteBlock
    {E : Type*} [TopologicalSpace E] (w : Weight) (S : Finset ℤ)
    (f : E → ℤ → ℂ) (x : E)
    (hf : ∀ n ∈ S, ContinuousAt (fun y => f y n) x) :
    ContinuousAt (fun y => finiteBlock (p := p) w S (f y)) x := by
  unfold finiteBlock
  apply tendsto_finsetSum S
  intro n hn
  exact (hf n hn).smul continuousAt_const

end NLS.WeightedCoeff
