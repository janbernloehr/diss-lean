import NLS.SequenceSpaces.PhaseRotation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Hilbert energy near a nonsquare-summable limit

Finite partial energies force the squared Hilbert norms of every
pointwise approximation to diverge. The same holds for the half-sum
energy of coordinate pairs, including the real Birkhoff mass expression.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- Every Hilbert-sequence approximation to a nonsquare-summable pointwise
limit has diverging energy; finite-gap or smooth hypotheses are unnecessary. -/
theorem tendsto_energy_atTop_of_nonsummable_limit {ι : Type*} {l : Filter ι}
    (a : ℤ → ℂ) (ha : ¬ Summable (fun n => ‖a n‖ ^ 2)) (z : ι → Coeff 2)
    (hz : ∀ n, Tendsto (fun j => z j n) l (𝓝 (a n))) :
    Tendsto (fun j => ‖z j‖ ^ 2) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hex : ∃ S : Finset ℤ, b < ∑ n ∈ S, ‖a n‖ ^ 2 := by
    by_contra h
    push Not at h
    exact ha (summable_of_sum_le (fun _ => sq_nonneg _) h)
  obtain ⟨S,hS⟩ := hex
  have ht := tendsto_finsetSum S (fun n _ => (hz n).norm.pow 2)
  filter_upwards [ht.eventually (lt_mem_nhds hS)] with j hj
  have hnorm := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (z j) S
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at hnorm
  exact hj.le.trans hnorm

/-- The literal half-sum energy of Hilbert coordinate pairs diverges whenever
one pointwise limiting component is not square summable. -/
theorem tendsto_pair_energy_atTop_of_nonsummable_limit {ι : Type*} {l : Filter ι}
    (a : ℤ → ℂ) (ha : ¬ Summable (fun n => ‖a n‖ ^ 2)) (z : ι → Coeff 2 × Coeff 2)
    (hz : ∀ n, Tendsto (fun j => (z j).1 n) l (𝓝 (a n))) :
    Tendsto (fun j => (‖(z j).1‖ ^ 2+‖(z j).2‖ ^ 2)/2) l atTop := by
  have ht := tendsto_energy_atTop_of_nonsummable_limit a ha (fun j => (z j).1) hz
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [ht.eventually (eventually_ge_atTop (2*b))] with j hj
  nlinarith [sq_nonneg ‖(z j).2‖]

end NLS.Coeff
