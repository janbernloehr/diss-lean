import NLS.ZakharovShabat.SourceDiagonalActionRatioSequence
import NLS.ZakharovShabat.SourceDiagonalActionRoot

/-! # One analytic domain for all positive physical action roots

The actual scaled ratios form an analytic bounded sequence. Its norm
continuity and the uniform real lower bound give a common complex
positive-real-part neighborhood. All positive-index principal roots
are analytic there and have uniform inverse-square-root decay.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sourceDiagonalActionRoot_allIndices_analytic_bound
    (φ : realDiagonalSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      (∀ n : ℤ, 0 < n → AnalyticOnNhd ℂ (sourceDiagonalActionRoot (by simp) (by norm_num) n) U) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U, ∀ n : ℤ, 0 < n →
        (Weight.sobolev (1/2) n)*‖sourceDiagonalActionRoot (by simp) (by norm_num) n ψ‖ ≤ R := by
  obtain ⟨A,hA,hφA,hF,he⟩ := exists_local_sourceDiagonalActionRatioSequence_analytic φ
  obtain ⟨B,hB,hφB,hρ,K,hK,hbound⟩ := exists_local_hilbert_diagonalActionRatio_analytic_inverse_bound φ
  obtain ⟨c,hc,hbase⟩ := exists_diagonalActionRatio_scaled_re_lower_bound φ
  let d := min c 1
  have hd : 0 < d := lt_min hc zero_lt_one
  have hbaseAll (n : ℤ) : d ≤ (sourceDiagonalActionRatioSequence φ.val n).re := by
    rw [he φ.val hφA n,sourceDiagonalScaledActionRatio]
    split_ifs with hn
    · exact (min_le_left c 1).trans (hbase n hn)
    · simpa only [one_re] using min_le_right c (1 : ℝ)
  have hnear : ∀ᶠ ψ : CoeffPair 2 in 𝓝 φ.val,
      ψ ∈ A ∩ B ∧ ‖sourceDiagonalActionRatioSequence ψ-sourceDiagonalActionRatioSequence φ.val‖ < d/2 := by
    have hf := (hF φ.val hφA).continuousAt.eventually
      (Metric.ball_mem_nhds (sourceDiagonalActionRatioSequence φ.val) (half_pos hd))
    filter_upwards [(hA.inter hB).mem_nhds ⟨hφA,hφB⟩,hf] with ψ hψ hψF
    exact ⟨hψ,by simpa only [mem_ball,dist_eq_norm] using hψF⟩
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  have hpos (ψ : CoeffPair 2) (hψ : ψ ∈ U) (n : ℤ) (hn : 0 < n) :
      0 < (sourceDiagonalActionRatio (by simp) (by norm_num) n ψ).re := by
    have hclose : ‖sourceDiagonalActionRatioSequence ψ n-sourceDiagonalActionRatioSequence φ.val n‖ < d/2 := by
      have hp := lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0)
        (sourceDiagonalActionRatioSequence ψ-sourceDiagonalActionRatioSequence φ.val) n
      exact hp.trans_lt (hUsub hψ).2
    have hre := (abs_le.mp (Complex.abs_re_le_norm
      (sourceDiagonalActionRatioSequence ψ n-sourceDiagonalActionRatioSequence φ.val n))).1
    simp only [Complex.sub_re] at hre
    have hscaled : 0 < (sourceDiagonalActionRatioSequence ψ n).re := by
      linarith [hbaseAll n]
    rw [he ψ (hUsub hψ).1.1 n,sourceDiagonalScaledActionRatio,if_pos hn] at hscaled
    have heq : ((((1+|(n : ℝ)| : ℝ) : ℂ)*sourceDiagonalActionRatio (by simp) (by norm_num) n ψ)).re =
        (1+|(n : ℝ)|)*(sourceDiagonalActionRatio (by simp) (by norm_num) n ψ).re := by simp
    rw [heq] at hscaled
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 1+|(n : ℝ)|)).mp hscaled
  refine ⟨U,hU,hφU,?_,Real.sqrt K,Real.sqrt_nonneg K,?_⟩
  · intro n hn ψ hψ
    have hs : sourceDiagonalActionRatio (by simp) (by norm_num) n ψ ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hpos ψ hψ n hn))
    exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)).comp
      (hρ n (ne_of_gt hn) ψ (hUsub hψ).1.2)
  · intro ψ hψ n hn
    have hw : Weight.sobolev (1/2) n = Real.sqrt (1+|(n : ℝ)|) := by
      rw [Weight.sobolev_apply,Real.sqrt_eq_rpow]
    have hsq := congrArg norm (sourceDiagonalActionRoot_sq (by simp) (by norm_num) n ψ)
    rw [norm_pow] at hsq
    have hsqBound : ((Weight.sobolev (1/2) n)*‖sourceDiagonalActionRoot (by simp) (by norm_num) n ψ‖)^2 ≤ (Real.sqrt K)^2 := by
      rw [hw,mul_pow,Real.sq_sqrt (by positivity),hsq,Real.sq_sqrt hK.le]
      exact (mul_le_mul_of_nonneg_left (hbound ψ (hUsub hψ).1.2 n (ne_of_gt hn)) (by positivity)).trans_eq (by field_simp)
    exact (sq_le_sq₀ (mul_nonneg ((Weight.sobolev (1/2)).positive n).le (norm_nonneg _))
      (Real.sqrt_nonneg K)).mp hsqBound

end NLS.ZakharovShabat
