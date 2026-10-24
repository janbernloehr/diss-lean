import NLS.ZakharovShabat.SourceHilbertGlobalInverse
import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport
import NLS.SequenceSpaces.DominatedCompactness

/-! # Compact containers for bounded sources with a fixed finite gap support

The actual Hilbert Birkhoff homeomorphism preserves the squared norm and
identifies open gaps with coordinate support. A finite coordinate majorant
therefore gives a compact container for each bounded source family with a
common finite set of possible open gaps.
-/
noncomputable section
open Set Complex NLS
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Bounded Hilbert sources with a common finite gap support lie in one norm-compact set. -/
theorem exists_compact_source_container_of_finite_gap_support
    (S : Finset ℤ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : Set (realTypeSourceSubmodule 2), IsCompact K ∧
      ∀ φ : realTypeSourceSubmodule 2, ‖φ.val‖ ≤ R →
      (∀ n ∉ S, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0) → φ ∈ K := by
  classical
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let e := D.hilbertRealHomeomorph
  let b : RealCoeff 2 := ∑ n ∈ S, lp.single 2 n R
  have hb (n : ℤ) : b n = if n ∈ S then R else 0 := by
    change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) 2 n) (∑ j ∈ S, lp.single 2 j R) = _
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  let T : Set (RealCoeff 2) := {u | ∀ n : ℤ, ‖u n‖ ≤ ‖b n‖}
  have hT : IsCompact T := by
    apply RealCoeff.isCompact_of_isClosed_of_majorant (by simp) b
    · simp only [T,ofPred_forall]
      exact isClosed_iInter fun n => isClosed_le
        ((lp.evalCLM ℝ (fun _ : ℤ => ℝ) 2 n).continuous.norm) continuous_const
    · intro u hu
      exact hu
  refine ⟨e.symm '' (T ×ˢ T),(hT.prod hT).image e.symm.continuous,?_⟩
  intro φ hφ hclosed
  have hnorm := D.hilbert_real_map_norm_sq φ
  have h₁ : ‖(e φ).1‖ ≤ R := by
    change ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1‖ ≤ R
    nlinarith [sq_nonneg ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2‖,
      norm_nonneg (sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1,norm_nonneg φ.val]
  have h₂ : ‖(e φ).2‖ ≤ R := by
    change ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2‖ ≤ R
    nlinarith [sq_nonneg ‖(sourceRealBirkhoffMap (by simp) (by norm_num) s φ).1‖,
      norm_nonneg (sourceRealBirkhoffMap (by simp) (by norm_num) s φ).2,norm_nonneg φ.val]
  have hzero (n : ℤ) (hn : n ∉ S) : (e φ).1 n = 0 ∧ (e φ).2 n = 0 :=
    (D.real_coordinates_zero_iff_gap_zero φ n).mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hclosed n hn)
  refine ⟨e φ,⟨?_,?_⟩,e.symm_apply_apply φ⟩
  · intro n
    by_cases hn : n ∈ S
    · rw [hb,if_pos hn,Real.norm_of_nonneg hR]
      exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (e φ).1 n).trans h₁
    · simp only [(hzero n hn).1,hb,if_neg hn,norm_zero,le_refl]
  · intro n
    by_cases hn : n ∈ S
    · rw [hb,if_pos hn,Real.norm_of_nonneg hR]
      exact (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (e φ).2 n).trans h₂
    · simp only [(hzero n hn).2,hb,if_neg hn,norm_zero,le_refl]

end NLS.ZakharovShabat
