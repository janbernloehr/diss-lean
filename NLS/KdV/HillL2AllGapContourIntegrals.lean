import NLS.KdV.HillRealGapContours
import NLS.ComplexAnalysis.RealCutCircleIntegral
import NLS.ComplexAnalysis.BoundedPuncturedCircleIntegral

/-! # Actual contour-to-gap identities at every real Hill gap

The intrinsic isolating circle uses neighboring band lengths rather
than a high-energy cutoff. Compact bounds and the full indexed boundary
jump identify every polynomial primitive moment with its real arcosh
integral. Collapsed gaps have a bounded removable puncture.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem circleIntegral_hillL2RealCutPrimitive_shifted
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    (∮ z in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
      z ^ m * (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi)) =
      -2 * ∫ x in (hillRealLabels q hq hr (2 * n - 1))..(hillRealLabels q hq hr (2 * n)),
        (x : ℂ) ^ m * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by
  let a := hillRealLabels q hq hr (2 * n - 1)
  let b := hillRealLabels q hq hr (2 * n)
  let c := hillRealGapCenter q hq hr n
  let d := hillRealGapHalfLength q hq hr n
  let η := hillRealGapCollar q hq hr n
  let f : ℂ → ℂ := fun z => z ^ m *
    (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z + I * (n : ℂ) * Real.pi)
  let φ : ℝ → ℂ := fun x => (x : ℂ) ^ m * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ)
  obtain ⟨hd, hη, hl, hu, hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  change 0 ≤ d at hd
  change 0 < η at hη
  change c - d = a at hl
  change c + d = b at hu
  have hf : AnalyticOnNhd ℂ f (ball (c : ℂ) (d + 2 * η) \ segment ℝ (a : ℂ) b) :=
    (analyticOnNhd_id.pow m).mul
      (((analyticOnNhd_hillL2RealCutPrimitive q hq hr).mono hsub).add analyticOnNhd_const)
  obtain ⟨M, hM, hbound⟩ := exists_bound_hillL2RealCutPrimitive_shifted q hq hr n m c (d + 2 * η)
  by_cases hd0 : d = 0
  · have ha : a = c := by linarith
    have hb : b = c := by linarith
    have hf0 : AnalyticOnNhd ℂ f (ball (c : ℂ) (2 * η) \ {(c : ℂ)}) := by
      simpa only [hd0, zero_add, ha, hb, segment_same] using hf
    have hz := circleIntegral_eq_zero_of_bounded_puncture f c η (2 * η) M hη (by linarith) hf0
      (fun z hz => hbound z (by simpa only [hd0, zero_add] using ball_subset_closedBall hz.1))
    change (∮ z in C((c : ℂ), d + η), f z) = -2 * ∫ x in a..b, φ x
    simpa only [hd0, zero_add, ha, hb, intervalIntegral.integral_same, mul_zero] using hz
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hφ : ContinuousOn φ (Icc a b) := (Complex.continuous_ofReal.pow m).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn (continuousOn_hillRealGapProfile q hq hr n hn))
    have hlower (x : ℝ) (hx : x ∈ Icc a b) :
        Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-φ x)) := by
      have hp := (tendsto_hillL2ContinuedPrimitive_gap_lower q hq hr n hn x hx).add_const
        (I * (n : ℂ) * Real.pi)
      simp only [sub_add_cancel] at hp
      have ht := ((continuousAt_id.pow m).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}) (a := (x : ℂ)))).mul hp
      have ht' : Tendsto (fun z : ℂ => z ^ m *
          (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q) + I * (n : ℂ) * Real.pi))
          (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (-φ x)) := by
        simpa only [φ, mul_neg, Pi.pow_apply, id_eq] using ht
      apply ht'.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [f, hillL2RealCutPrimitive, if_neg hz.ne]
    have hupper (x : ℝ) (hx : x ∈ Icc a b) :
        Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (φ x)) := by
      have hp := (tendsto_hillL2ContinuedPrimitive_gap_upper q hq hr n hn x hx).add_const
        (I * (n : ℂ) * Real.pi)
      simp only [sub_add_cancel] at hp
      have ht := ((continuousAt_id.pow m).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {z : ℂ | 0 < z.im}) (a := (x : ℂ)))).mul hp
      simp only [Pi.pow_apply, id_eq] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [f, hillL2RealCutPrimitive, if_neg hz.ne']
    have he := circleIntegral_eq_neg_real_cut_jump f (fun x => -φ x) φ c d (d + η) (d + 2 * η) M
      hdpos (by linarith) (by linarith) hM
      (by rw [hl, hu]; exact hf)
      (by
        intro z hz
        exact hbound z ((closedBall_subset_closedBall (by linarith : d + η ≤ d + 2 * η)) hz.1))
      (by rw [hl, hu]; exact hφ.neg) (by rw [hl, hu]; exact hφ)
      (by simpa only [hl, hu] using hlower) (by simpa only [hl, hu] using hupper)
    change (∮ z in C((c : ℂ), d + η), f z) = -2 * ∫ x in a..b, φ x
    rw [he, hl, hu]
    simp_rw [show ∀ x, φ x - -φ x = (2 : ℂ) * φ x by intro x; ring]
    rw [intervalIntegral.integral_const_mul]
    ring

end NLS.KdV
