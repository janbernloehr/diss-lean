import NLS.ZakharovShabat.SourceDiagonalNormalizedLaurentCommonDomain
import NLS.ZakharovShabat.SourceDiagonalLaurentZeroBound
import NLS.ZakharovShabat.SourceNormalizedActionUniformBound
import NLS.ZakharovShabat.SourceNormalizedActionComplexUniformPositive

/-! # Uniform decay of normalized inverse-frequency action factors

Open gaps permit cancellation in the existing actual Laurent estimate.
At a closed complex gap the exact midpoint formula gives the same
inverse-frequency decay. One complex neighborhood and bound work for
all noncentral indices, without an open-gap assumption.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_hilbert_normalizedDiagonalLaurent_inverse_bound
    (φ : realDiagonalSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ U, ∀ n : ℤ, n ≠ 0 →
        ‖sourceNormalizedDiagonalLaurentAction (by simp) (by norm_num) n ψ‖ ≤ K/(1+|(n : ℝ)|) := by
  let C := (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).localChart φ
  have hφC := C.source_subset (mem_ball_self C.radius_pos)
  obtain ⟨D,hD,hd⟩ := C.cauchy.exists_diagonal_gapPoint_inverse_bound φ hφC
  obtain ⟨A,hA,hφA,_,K,hK,hact⟩ :=
    (sourceDiagonalLaurentAtlas (by simp) (by norm_num)).exists_local_zeroLevel_inverse_frequency_bound φ
  obtain ⟨B,hB,hφB,M,hM,hg⟩ := exists_local_hilbert_normalizedAction_uniform_bound φ.val φ.property.1
  refine ⟨A ∩ (B ∩ ball φ.val C.radius),hA.inter (hB.inter isOpen_ball),
    ⟨hφA,hφB,mem_ball_self C.radius_pos⟩,K+D*M,by positivity,?_⟩
  intro ψ hψ n hn
  have hw : 0 < 1+|(n : ℝ)| := by positivity
  by_cases hgap : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) n = 0
  · have ht : ‖(sourceStandardRootMidpoint (by simp) (by norm_num) ψ n)⁻¹‖ ≤ D/(1+|(n : ℝ)|) := by
      simpa only [Real.cos_pi_div_two,ofReal_zero,mul_zero,add_zero] using
        hd ψ (C.source_subset hψ.2.2) n hn (Real.pi/2)
    rw [sourceNormalizedDiagonalLaurentAction,if_pos hgap,norm_mul]
    calc
      _ ≤ (D/(1+|(n : ℝ)|))*M := mul_le_mul ht (hg ψ hψ.2.1 n) (norm_nonneg _) (by positivity)
      _ ≤ _ := by apply (le_div_iff₀ hw).mpr; field_simp; nlinarith
  · have hbound := hact ψ hψ.1 n hn
    rw [sourceNormalizedDiagonalLaurentAction,if_neg hgap,norm_div,norm_pow]
    rw [sourcePeriodicGapDisplacement_apply] at hbound
    calc
      _ ≤ K/(1+|(n : ℝ)|) := (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hgap) 2)).mpr hbound
      _ ≤ _ := (div_le_div_iff_of_pos_right hw).mpr (le_add_of_nonneg_right (mul_nonneg hD.le hM))

/-- One complex domain supports every regularized ratio, with its correct
inverse-frequency bound. No selected gap is required to be open. -/
theorem exists_local_hilbert_diagonalActionRatio_analytic_inverse_bound
    (φ : realDiagonalSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      (∀ n : ℤ, n ≠ 0 → AnalyticOnNhd ℂ (sourceDiagonalActionRatio (by simp) (by norm_num) n) U) ∧
      ∃ K : ℝ, 0 < K ∧ ∀ ψ ∈ U, ∀ n : ℤ, n ≠ 0 →
        ‖sourceDiagonalActionRatio (by simp) (by norm_num) n ψ‖ ≤ K/(1+|(n : ℝ)|) := by
  obtain ⟨A,hA,hφA,hAn,_⟩ :=
    exists_local_sourceNormalizedDiagonalLaurentAction_allIndices_analytic_factor (by simp) (by norm_num) φ
  obtain ⟨B,hB,hφB,hBn,_⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor (by simp) (by norm_num) φ.val φ.property.1
  obtain ⟨C,hC,hφC,K,hK,hbound⟩ := exists_local_hilbert_normalizedDiagonalLaurent_inverse_bound φ
  obtain ⟨D,hD,hφD,c,hc,hpos⟩ := exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos
    (p := 2) (q := 2) (by simp) (by norm_num) (by norm_num) (by simp) (by norm_num) φ.val φ.property.1
  let U := (A ∩ B) ∩ (C ∩ D)
  have hden (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) :
      c/2 ≤ ‖2*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ‖ := by
    have h := (hpos ψ hψ.2.2 n).trans (Complex.re_le_norm _)
    simp only [norm_mul,Complex.norm_ofNat] at h
    rw [norm_mul,Complex.norm_ofNat]
    linarith
  have hne (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) :
      2*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ ≠ 0 := by
    exact norm_pos_iff.mp ((half_pos hc).trans_le (hden ψ hψ n))
  refine ⟨U,(hA.inter hB).inter (hC.inter hD),⟨⟨hφA,hφB⟩,hφC,hφD⟩,?_,2*K/c,by positivity,?_⟩
  · intro n hn ψ hψ
    exact (hAn n hn ψ hψ.1.1).div (analyticAt_const.mul (hBn n ψ hψ.1.2)) (hne ψ hψ n)
  · intro ψ hψ n hn
    rw [sourceDiagonalActionRatio,norm_div]
    calc
      _ ≤ (K/(1+|(n : ℝ)|))/(c/2) := div_le_div₀ (by positivity) (hbound ψ hψ.2.1 n hn)
        (half_pos hc) (hden ψ hψ n)
      _ = _ := by field_simp

end NLS.ZakharovShabat
