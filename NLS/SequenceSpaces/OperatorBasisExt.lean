import NLS.SequenceSpaces.Truncation

/-!
# Continuous linear maps determined by the Fourier basis

For finite Banach exponents, finite Fourier truncations converge in
norm. Agreement on the unit coordinate vectors thus determines a
continuous linear map on the whole coefficient space.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Continuous linear maps on finite `ℓᵖ` agree if they agree on every
unit Fourier coordinate vector. -/
theorem continuousLinearMap_eq_of_single (hp : p ≠ ⊤)
    (A B : Coeff p →L[ℂ] E)
    (hentry : ∀ k : ℤ, A (lp.single p k 1) = B (lp.single p k 1)) :
    A = B := by
  classical
  apply ContinuousLinearMap.ext
  intro h
  have hsingle (k : ℤ) : A (lp.single p k (h k)) = B (lp.single p k (h k)) := by
    have heq : (lp.single p k (h k) : Coeff p) = h k • lp.single p k 1 := by
      ext m
      by_cases hmk : m = k <;> simp [lp.single_apply, hmk]
    rw [heq, map_smul, map_smul, hentry]
  have hfinite (s : Finset ℤ) : A (truncate s h) = B (truncate s h) := by
    simp only [truncate, map_sum]
    exact Finset.sum_congr rfl (fun k _ => hsingle k)
  have hA := (A.continuous.tendsto h).comp (tendsto_truncate hp h)
  have hB := (B.continuous.tendsto h).comp (tendsto_truncate hp h)
  exact tendsto_nhds_unique hA (hB.congr (fun s => (hfinite s).symm))

end NLS.Coeff
