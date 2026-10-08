import NLS.ComplexAnalysis.ZeroCountComparison
import NLS.ZakharovShabat.LinearWeightDeterminantBounds

/-! # Two determinant zeros at the explicit quadratic threshold

The count uses analytic orders, so a repeated root has multiplicity two.
No additional frequency cutoff or reality assumption is imposed.
-/
noncomputable section
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Lemma 25.4's determinant count on the whole strip, with exact analytic multiplicity. -/
theorem linearWeight_determinant_zeroCount (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    AnalyticOnNhd ℂ (resonantDeterminantExtension (by simp) w φ n) (resonantStrip n) ∧
    (∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
      resonantDeterminantExtension (by simp) w φ n z ≠ 0) ∧
    (resonantStrip n ∩ (resonantDeterminantExtension (by simp) w φ n) ⁻¹' {0}).Finite ∧
    (∀ z ∈ resonantStrip n, analyticOrderAt (resonantDeterminantExtension (by simp) w φ n) z ≠ ⊤) ∧
    analyticZeroCount (resonantDeterminantExtension (by simp) w φ n)
      (Metric.closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) = 2 ∧
    analyticZeroCount (resonantDeterminantExtension (by simp) w φ n) (refinedResonantDisk n) = 2 ∧
    analyticZeroCount (resonantDeterminantExtension (by simp) w φ n) (resonantStrip n) = 2 := by
  have ha : AnalyticOnNhd ℂ (resonantDeterminantExtension (by simp) w φ n) (resonantStrip n) :=
    fun z hz => analyticAt_resonantDeterminantExtension_spectral (by simp) w φ n z
      (mem_weightedCorrectionDomain_linear w hw φ n z hz hn)
  have hloc := linearWeight_determinant_root_localization w hw φ n hn
  have hcomp := linearWeight_determinant_boundary_lt w hw φ n hn
  have hr : 0 < Real.pi/4 := by positivity
  have hsub := closedBall_subset_resonantStrip n (by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2)
  have had := ha.mono hsub
  have hboundary : ∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
      resonantDeterminantExtension (by simp) w φ n z ≠ 0 :=
    fun z hz => (rouche_ratio_mem_slitPlane (hcomp z hz)).2.1
  have hclosed := analyticZeroCount_eq_degree_of_boundary_lt 2 hr had hcomp
  have hopen : analyticZeroCount (resonantDeterminantExtension (by simp) w φ n) (refinedResonantDisk n) = 2 := by
    rw [refinedResonantDisk, analyticZeroCount_ball_eq_closedBall hboundary, hclosed]
  have heq : resonantStrip n ∩ (resonantDeterminantExtension (by simp) w φ n) ⁻¹' {0} =
      Metric.closedBall ((Real.pi : ℂ)*n) (Real.pi/4) ∩
        (resonantDeterminantExtension (by simp) w φ n) ⁻¹' {0} := by
    ext z
    exact ⟨fun hz => ⟨Metric.ball_subset_closedBall (hloc z hz.1 hz.2).2,hz.2⟩,
      fun hz => ⟨hsub hz.1,hz.2⟩⟩
  obtain ⟨b,hbm⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := (Real.pi : ℂ)*n) |>.mpr hr.le
  have hbclosed := Metric.sphere_subset_closedBall hbm
  have hbf := hboundary b hbm
  refine ⟨ha,hboundary,?_,?_,hclosed,hopen,?_⟩
  · rw [heq]
    exact finite_analytic_zeros (isCompact_closedBall _ _) (Metric.isConnected_closedBall hr.le) had hbclosed hbf
  · intro z hz
    by_cases hfz : resonantDeterminantExtension (by simp) w φ n z = 0
    · exact analyticOrderAt_ne_top_on_connected (Metric.isConnected_closedBall hr.le).isPreconnected
        had hbclosed hbf (Metric.ball_subset_closedBall (hloc z hz hfz).2)
    · rw [(ha z hz).analyticOrderAt_eq_zero.mpr hfz]
      exact ENat.zero_ne_top
  · rw [analyticZeroCount_congr_set (resonantDeterminantExtension (by simp) w φ n)
      (K := resonantStrip n) (L := refinedResonantDisk n)
      (fun z hz => ⟨fun hs => (hloc z hs hz).2, fun hd => refinedResonantDisk_subset_strip n hd⟩), hopen]


/-- The smaller closed source disc itself contains total analytic multiplicity two. -/
theorem linearWeight_determinant_sourceDisc_zeroCount (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    analyticZeroCount (resonantDeterminantExtension (by simp) w φ n)
      (Metric.closedBall ((Real.pi:ℂ)*n) (quadraticLocalizationRadius ‖φ‖ n)) = 2 := by
  have hsub := closedBall_subset_resonantStrip n
    ((quadraticLocalizationRadius_lt_pi_div_five (norm_nonneg _) n hn).le.trans
      (by linarith [Real.pi_pos] : Real.pi/5 ≤ Real.pi/2))
  rw [analyticZeroCount_congr_set (resonantDeterminantExtension (by simp) w φ n)
    (K := Metric.closedBall ((Real.pi:ℂ)*n) (quadraticLocalizationRadius ‖φ‖ n))
    (L := resonantStrip n) (fun z hz => ⟨fun hd => hsub hd, fun hs => ?_⟩)]
  · exact (linearWeight_determinant_zeroCount w hw φ n hn).2.2.2.2.2.2
  · exact Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using
      (linearWeight_determinant_root_localization w hw φ n hn z hs hz).1)

end NLS.ZakharovShabat
