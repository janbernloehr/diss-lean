import NLS.Fourier.ShiftedExponentialCoefficientBound
import Mathlib.Analysis.Asymptotics.Defs

/-! # Lemma E.3: uniform Fourier-Lebesgue bounds for shifted exponentials

The tail constant depends only on q>1, including q=infinity. The
arbitrary finite head has finite norms and is absorbed into a global
bound. No real-frequency or endpoint-matching condition is imposed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A common positive tail bound, chosen before the frequency sequence and cutoff. -/
def sourceLemmaE3Bound (hq : 1 < q) : ℝ :=
  (2+5*Real.pi/4)*Real.exp (5*Real.pi/4)*unitIntervalC1FourierConstant hq+1

theorem sourceLemmaE3Bound_pos (hq : 1 < q) : 0 < sourceLemmaE3Bound hq := by
  have hc := unitIntervalC1FourierConstant_nonneg hq
  unfold sourceLemmaE3Bound
  positivity

/-- The same constant controls every frequency in every prescribed pi/4 tail. -/
theorem sourceLemmaE3_tail (hq : 1 < q) (ν : ℤ → ℂ) (N : ℕ)
    (hν : ∀ n : ℤ, N ≤ n.natAbs → ‖ν n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ∀ n : ℤ, N ≤ n.natAbs → ‖exponentialFourierCoefficients hq (ν n)‖ ≤ sourceLemmaE3Bound hq := by
  intro n hn
  have h := norm_exponentialFourierCoefficients_near_lattice hq n (ν n) (hν n hn)
  unfold sourceLemmaE3Bound
  linarith

/-- E.3 as a global norm bound. The finite head is unrestricted and absorbed into the constant. -/
theorem sourceLemmaE3 (hq : 1 < q) (ν : ℤ → ℂ)
    (hν : ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖ν n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ‖exponentialFourierCoefficients hq (ν n)‖ ≤ C := by
  obtain ⟨N,hN⟩ := hν
  let H := Finset.Icc (-(N:ℤ)) (N:ℤ)
  let S := ∑ n ∈ H, ‖exponentialFourierCoefficients hq (ν n)‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hC := sourceLemmaE3Bound_pos hq
  refine ⟨sourceLemmaE3Bound hq+S,by positivity,?_⟩
  intro n
  by_cases hn : N ≤ n.natAbs
  · exact (sourceLemmaE3_tail hq ν N hN n hn).trans (le_add_of_nonneg_right hS)
  · have hnH : n ∈ H := by
      dsimp only [H]
      simp only [Finset.mem_Icc]
      omega
    have hle : ‖exponentialFourierCoefficients hq (ν n)‖ ≤ S :=
      Finset.single_le_sum (fun j _ => norm_nonneg (exponentialFourierCoefficients hq (ν j))) hnH
    exact hle.trans (le_add_of_nonneg_left hC.le)

/-- The literal O(1) formulation as the absolute lattice index tends to infinity. -/
theorem sourceLemmaE3_bigO (hq : 1 < q) (ν : ℤ → ℂ)
    (hν : ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖ν n-(Real.pi:ℂ)*n‖ ≤ Real.pi/4) :
    Asymptotics.IsBigO (Filter.comap Int.natAbs atTop)
      (fun n : ℤ => exponentialFourierCoefficients hq (ν n)) (fun _ : ℤ => (1:ℝ)) := by
  obtain ⟨C,_,hC⟩ := sourceLemmaE3 hq ν hν
  apply Asymptotics.IsBigO.of_bound C
  exact Filter.Eventually.of_forall (fun n => by simpa using hC n)

end NLS.Fourier
