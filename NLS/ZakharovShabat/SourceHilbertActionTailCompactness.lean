import NLS.ZakharovShabat.SourceHilbertProperness
import NLS.SequenceSpaces.DominatedCompactness

/-! # Actual source norm compactness from one summable action-tail bound

The actual ordinary action map is proper. Its exact mass trace bounds
finitely many low actions; one nonnegative ell1 majorant controls the
entire high tail. Thus a norm bound and that genuine tail comparison
place the original real Hilbert sources in one norm-compact set.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- A fixed summable high-action majorant and a source norm bound give
an ACTUAL strong compact container. No inverse or no-loss premise remains. -/
theorem exists_compact_source_container_of_bounded_action_tail
    (R : ℝ) (N : ℕ) (b : RealCoeff 1) (hb : ∀ j : ℤ, 0≤b j) :
    ∃ K : Set (realTypeSourceSubmodule 2), IsCompact K ∧
      ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖≤R →
      (∀ j : ℤ, N≤j.natAbs →
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property j).re≤b j) → φ∈K := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let head : RealCoeff 1 := ∑ j ∈ S, lp.single 1 j (R^2/2)
  have hhead (j : ℤ) : head j=if j∈S then R^2/2 else 0 := by
    change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) 1 j) (∑ k ∈ S, lp.single 1 k (R^2/2))=_
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  have hhpos (j : ℤ) : 0≤head j := by rw [hhead]; split_ifs <;> positivity
  let c : RealCoeff 1 := head+b
  have hcpos (j : ℤ) : 0≤c j := add_nonneg (hhpos j) (hb j)
  let T : Set (RealCoeff 1) := {a | ∀ j : ℤ, ‖a j‖≤‖c j‖}
  have hT : IsCompact T := by
    apply RealCoeff.isCompact_of_isClosed_of_majorant (by simp) c
    · simp only [T,ofPred_forall]
      exact isClosed_iInter (fun j => isClosed_le
        ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) 1 j).continuous.norm) continuous_const)
    · intro a ha; exact ha
  refine ⟨(sourceHilbertRealActionSequence s) ⁻¹' T,
    (isProperMap_iff_isCompact_preimage.mp D.hilbert_realActionSequence_proper).2 hT,?_⟩
  intro φ hφ htail
  change ∀ j : ℤ, ‖sourceHilbertRealActionSequence s φ j‖≤‖c j‖
  intro j
  rw [D.hilbert_realActionSequence_apply,Real.norm_of_nonneg
    (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property j).1,
    Real.norm_of_nonneg (hcpos j)]
  by_cases hj : j∈S
  · have h := lp.norm_apply_le_norm (by norm_num : (1 : ℝ≥0∞)≠0) (sourceHilbertRealActionSequence s φ) j
    rw [D.hilbert_realActionSequence_apply,D.hilbert_realActionSequence_norm_eq_half_norm_sq,
      Real.norm_of_nonneg (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
        (by simp) (by norm_num) φ.val φ.property j).1] at h
    have hn : ‖φ‖^2≤R^2 := pow_le_pow_left₀ (norm_nonneg _) hφ 2
    change _≤head j+b j
    rw [hhead,if_pos hj]
    linarith [hb j]
  · have hn : N≤j.natAbs := by dsimp only [S] at hj; simp only [Finset.mem_Icc] at hj; omega
    change _≤head j+b j
    exact (htail j hn).trans (le_add_of_nonneg_left (hhpos j))

end NLS.ZakharovShabat
