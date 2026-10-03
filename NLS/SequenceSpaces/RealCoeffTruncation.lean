import NLS.SequenceSpaces.RealCoeff
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Finite truncations of real Birkhoff output sequences -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- Keep the real Fourier coefficients in a finite set. -/
def truncate (S : Finset ℤ) (a : RealCoeff p) : RealCoeff p :=
  ∑ n ∈ S, lp.single p n (a n)

@[simp] theorem truncate_apply (S : Finset ℤ) (a : RealCoeff p) (n : ℤ) :
    truncate S a n = if n ∈ S then a n else 0 := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) p n) (∑ j ∈ S, lp.single p j (a j)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply, lp.single_apply, Pi.single_apply]

/-- Truncate both real output sequences at the same finite cutoff. -/
def truncatePair (S : Finset ℤ) (z : RealCoeff p × RealCoeff p) : RealCoeff p × RealCoeff p :=
  (truncate S z.1, truncate S z.2)

/-- The set of indices on which at least one output component is nonzero. -/
def pairSupport (z : RealCoeff p × RealCoeff p) : Set ℤ :=
  {n | z.1 n ≠ 0 ∨ z.2 n ≠ 0}

/-- Each truncation has finite output support. -/
theorem finite_pairSupport_truncatePair (S : Finset ℤ) (z : RealCoeff p × RealCoeff p) :
    (pairSupport (truncatePair S z)).Finite := by
  apply S.finite_toSet.subset
  intro n hn
  by_contra hnot
  change n ∉ S at hnot
  simp [pairSupport, truncatePair, hnot] at hn

/-- Finite real output truncations converge for every finite exponent. -/
theorem tendsto_truncatePair [Fact (1 ≤ p)] (hp : p ≠ ⊤) (z : RealCoeff p × RealCoeff p) :
    Tendsto (fun S : Finset ℤ => truncatePair S z) atTop (𝓝 z) :=
  (lp.hasSum_single hp z.1).prodMk_nhds (lp.hasSum_single hp z.2)

end NLS.RealCoeff
