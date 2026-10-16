import NLS.ZakharovShabat.CanonicalWeightedGapSummability
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2
import NLS.ZakharovShabat.SourceBirkhoffCoordinateBound

/-! # Weighted membership of the original real Birkhoff coordinates

For every finite p>1, weighted spectral gap summability and the exact real
action-radius identity imply weighted summability of both original coordinates.
This proves membership; it does not assert analyticity in the stronger norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Full weighted summability of the original periodic gaps, including the finite central set. -/
theorem sourceWeightedGap_mem (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : CoeffPair p) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : weightedBaseToPair w ψ = periodOnePotential φ) :
    Memℓp (fun n : ℤ => (w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 φ n) p := by
  obtain ⟨N, hN, U, _, hψU, htail⟩ := exists_uniform_canonicalWeightedGapSummability hp hp1 w ψ
  have heven : weightedBaseToPair w ψ ∈ pairParitySubspace 0 := by
    rw [hψ]
    exact periodOnePotential_mem _
  have hs := (htail ψ hψU heven N le_rfl).1
  let F : ℤ → ℝ := fun n => ‖(w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 φ n‖ ^ p.toReal
  have htailF : Summable (fun n : ℤ => if N ≤ n.natAbs then F n else 0) := by
    simpa only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (w.toWeight.positive _), Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _),
      hψ, sourcePeriodicGapDisplacement_apply] using hs
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hhead : Summable (fun n : ℤ => if N ≤ n.natAbs then 0 else F n) := by
    apply summable_of_ne_finset_zero (s := S)
    intro n hn
    have hn' : N ≤ n.natAbs := by
      simp only [S, Finset.mem_Icc] at hn
      omega
    simp only [if_pos hn']
  apply memℓp_gen
  change Summable F
  exact (htailF.add hhead).congr (fun n => by split_ifs <;> simp only [zero_add, add_zero])

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- A single constant bounds both real rectangular coordinates by the actual gap lengths. -/
theorem real_map_gap_bound (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℤ,
      |(sourceRealBirkhoffMap hp hp1 s φ).1 n| ≤ A * ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ ∧
      |(sourceRealBirkhoffMap hp hp1 s φ).2 n| ≤ A * ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ := by
  obtain ⟨U, _, hφU, A, hA, hb⟩ :=
    exists_local_uniform_sourceNormalizedActionRoot_bound hp hp1 φ.val φ.property
  obtain ⟨V, _, hφV, _, hf⟩ :=
    exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ.val φ.property
  refine ⟨A, hA, ?_⟩
  intro n
  obtain ⟨hIpos, hIim, _⟩ := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n
  have he : sourceRealAction hp hp1 φ.val φ.property n =
      ((sourceRealAction hp hp1 φ.val φ.property n).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hIim
  have hnI : ‖sourceComplexAction hp hp1 n φ.val‖ =
      (sourceRealAction hp hp1 φ.val φ.property n).re := by
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property, he]
    exact Complex.norm_of_nonneg hIpos
  have hx := congrArg norm (hf φ.val hφV n).1
  have hI := congrArg norm (hf φ.val hφV n).2
  norm_num only [norm_pow, norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at hx hI
  rw [hnI] at hI
  have hξ := hb φ.val hφU n
  have hξsq : ‖sourceNormalizedActionRoot hp hp1 n φ.val‖^2 ≤ A^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hξ 2
  have hrad := D.real_map_action_radius φ n
  have hmul := mul_le_mul_of_nonneg_left hξsq (sq_nonneg ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖)
  have hprod := congrArg (fun x : ℝ => ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖^2 * x) hx
  have hbound :
      ((sourceRealBirkhoffMap hp hp1 s φ).1 n)^2 + ((sourceRealBirkhoffMap hp hp1 s φ).2 n)^2 ≤
        (A * ‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖)^2 := by
    nlinarith [sq_nonneg ‖sourceNormalizedActionRoot hp hp1 n φ.val‖]
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA.le (norm_nonneg _))).mp
    simpa only [sq_abs] using le_trans (le_add_of_nonneg_right (sq_nonneg _)) hbound
  · apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA.le (norm_nonneg _))).mp
    simpa only [sq_abs] using le_trans (le_add_of_nonneg_left (sq_nonneg _)) hbound

/-- The original real Birkhoff coordinates retain every admissible source spectral weight. -/
theorem real_map_mem_weighted (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (φ : realTypeSourceSubmodule p)
    (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : weightedBaseToPair w ψ = periodOnePotential φ.val) :
    Memℓp (fun n : ℤ => w (2*n) * (sourceRealBirkhoffMap hp hp1 s φ).1 n) p ∧
    Memℓp (fun n : ℤ => w (2*n) * (sourceRealBirkhoffMap hp hp1 s φ).2 n) p := by
  obtain ⟨A, _, hb⟩ := D.real_map_gap_bound φ
  have hmajor := (sourceWeightedGap_mem hp hp1 w φ.val ψ hψ).norm.const_mul A
  constructor
  · apply hmajor.mono
    intro n
    simpa only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
      abs_of_pos (w.toWeight.positive _), mul_left_comm (w (2*n)) A] using
      (mul_le_mul_of_nonneg_left (hb n).1 (w.toWeight.positive (2*n)).le)
  · apply hmajor.mono
    intro n
    simpa only [norm_mul, Real.norm_eq_abs, Complex.norm_real,
      abs_of_pos (w.toWeight.positive _), mul_left_comm (w (2*n)) A] using
      (mul_le_mul_of_nonneg_left (hb n).2 (w.toWeight.positive (2*n)).le)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
