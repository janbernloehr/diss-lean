import NLS.SequenceSpaces.RealCoeffExponent
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Approximating nonnegative real actions by summable actions -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A finite truncation regarded as a summable sequence. -/
def finiteSummable (S : Finset ℤ) (b : RealCoeff q) : RealCoeff 1 :=
  ∑ n ∈ S, lp.single 1 n (b n)

omit [Fact (1 ≤ q)] in
@[simp] theorem finiteSummable_apply (S : Finset ℤ) (b : RealCoeff q) (n : ℤ) :
    finiteSummable S b n = if n ∈ S then b n else 0 := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) 1 n) (∑ j ∈ S, lp.single 1 j (b j)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]

omit [Fact (1 ≤ q)] in
/-- Finite approximation preserves nonnegativity. -/
theorem finiteSummable_nonneg (S : Finset ℤ) (b : RealCoeff q) (hb : ∀ n, 0 ≤ b n) :
    ∀ n, 0 ≤ finiteSummable S b n := by
  intro n
  simp only [finiteSummable_apply]
  split_ifs <;> simp_all

/-- The summable approximations converge in every finite target exponent. -/
theorem tendsto_complex_finiteSummable (hq : q ≠ ⊤) (b : RealCoeff q) :
    Tendsto (fun S : Finset ℤ => Coeff.exponentInclusion (Fact.out : 1 ≤ q)
      (complexCLM 1 (finiteSummable S b))) atTop (𝓝 (complexCLM q b)) := by
  have he (S : Finset ℤ) : Coeff.exponentInclusion (Fact.out : 1 ≤ q)
      (complexCLM 1 (finiteSummable S b)) = ∑ n ∈ S, lp.single q n ((b n : ℝ) : ℂ) := by
    ext n
    change (finiteSummable S b n : ℂ) =
      (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n) (∑ j ∈ S, lp.single q j (b j : ℂ))
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
    split_ifs <;> rfl
  simp_rw [he]
  exact lp.hasSum_single hq (complexCLM q b)

end NLS.RealCoeff
