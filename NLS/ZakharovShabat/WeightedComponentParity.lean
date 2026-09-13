import NLS.ZakharovShabat.WeightedCorrection
import NLS.FunctionalAnalysis.SquaredNeumannInvariant

/-!
# Component parity of the squared Neumann series

`T_n` exchanges the two physical components. Its even powers, and their
actual convergent sum, preserve each component subspace. This is component
parity, unrelated to parity of the integer Fourier frequency.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Vanishing of the second input component forces the first output component to vanish. -/
theorem weightedPotentialInverse_fst_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.snd = 0) :
    (weightedPotentialInverse hp w φ n z hz f).fst = 0 := by
  rw [weightedPotentialInverse_fst, hf, map_zero]
  exact (w.convolutionCLM φ.fst).map_zero

/-- Vanishing of the first input component forces the second output component to vanish. -/
theorem weightedPotentialInverse_snd_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.fst = 0) :
    (weightedPotentialInverse hp w φ n z hz f).snd = 0 := by
  rw [weightedPotentialInverse_snd, hf, map_zero]
  exact (w.convolutionCLM φ.snd).map_zero

/-- Every even power preserves the subspace with first component zero. -/
theorem weightedPotentialInverse_even_fst_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.fst = 0) (j : ℕ) :
    ((((weightedPotentialInverse hp w φ n z hz)^2)^j) f).fst = 0 := by
  induction j with
  | zero => simpa using hf
  | succ j hj =>
    rw [pow_succ', pow_two, mul_apply_eq_comp, mul_apply_eq_comp]
    exact weightedPotentialInverse_fst_eq_zero hp w φ n z hz _
      (weightedPotentialInverse_snd_eq_zero hp w φ n z hz _ hj)

/-- Every even power preserves the subspace with second component zero. -/
theorem weightedPotentialInverse_even_snd_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.snd = 0) (j : ℕ) :
    ((((weightedPotentialInverse hp w φ n z hz)^2)^j) f).snd = 0 := by
  induction j with
  | zero => simpa using hf
  | succ j hj =>
    rw [pow_succ', pow_two, mul_apply_eq_comp, mul_apply_eq_comp]
    exact weightedPotentialInverse_snd_eq_zero hp w φ n z hz _
      (weightedPotentialInverse_fst_eq_zero hp w φ n z hz _ hj)

/-- The even Neumann sum preserves vanishing of the first component. -/
theorem weightedEvenCorrection_fst_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.fst = 0) :
    (weightedEvenCorrection hp w φ n z hz h f).fst = 0 := by
  let E := WeightedCoeffPair w.toWeight p
  let π₁ : E →L[ℂ] WeightedCoeff w.toWeight p :=
    (ContinuousLinearMap.fst ℂ _ _).comp (WeightedCoeffPair.toMax w.toWeight p).toContinuousLinearMap
  exact SquaredNeumann.evenSeries_preserves_kernel
    (weightedPotentialInverse hp w φ n z hz) (weightedEvenCorrection hp w φ n z hz h)
    (weightedEvenCorrection_hasSum hp w φ n z hz h) π₁
    (fun a ha => weightedPotentialInverse_fst_eq_zero hp w φ n z hz _
      (weightedPotentialInverse_snd_eq_zero hp w φ n z hz a ha)) f hf

/-- The even Neumann sum preserves vanishing of the second component. -/
theorem weightedEvenCorrection_snd_eq_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (f : WeightedCoeffPair w.toWeight p) (hf : f.snd = 0) :
    (weightedEvenCorrection hp w φ n z hz h f).snd = 0 := by
  let E := WeightedCoeffPair w.toWeight p
  let π₂ : E →L[ℂ] WeightedCoeff w.toWeight p :=
    (ContinuousLinearMap.snd ℂ _ _).comp (WeightedCoeffPair.toMax w.toWeight p).toContinuousLinearMap
  exact SquaredNeumann.evenSeries_preserves_kernel
    (weightedPotentialInverse hp w φ n z hz) (weightedEvenCorrection hp w φ n z hz h)
    (weightedEvenCorrection_hasSum hp w φ n z hz h) π₂
    (fun a ha => weightedPotentialInverse_snd_eq_zero hp w φ n z hz _
      (weightedPotentialInverse_fst_eq_zero hp w φ n z hz a ha)) f hf

end NLS.ZakharovShabat
