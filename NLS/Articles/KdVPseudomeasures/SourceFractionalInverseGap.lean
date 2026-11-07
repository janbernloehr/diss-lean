import NLS.Articles.KdVPseudomeasures.EndpointNativeInverseRegularity
import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv

/-! Any actual fractional native output controls the same original
Hill gap sequence at the exact corresponding negative Hilbert order. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem originalCanonicalGaps_mem_sobolev_of_native_output
    (s : ℝ) (hs : s ≤ 0) (q : OriginalHminusOnePotential)
    (z : WeightedCoeff (Weight.signedSobolev (s+1/2)) 2)
    (hz : ∀ k, z.val k = hillHminusNativeCoordinate k (originalPeriodOneCoefficients q)) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*originalCanonicalGapValues q k) 2 := by
  let a := (signedOrderHalfFourierEquiv s 2).symm z
  obtain ⟨N,hN,hbound⟩ := exists_hillReal_native_inverse_gap_tail (originalHillRealMeanZeroSource q)
  have ha := a.property
  change Memℓp (fun k => (Weight.signedSobolev s k:ℂ)*a.val k) 2 at ha
  have hg : Memℓp (fun k => (Weight.signedSobolev s k:ℂ)*originalCanonicalGapValues q k) 2 := by
    apply NLS.memlp_of_natAbs_tail_norm_le _ _ ha N 3 (by norm_num)
    intro k hk
    have hk0 : k ≠ 0 := by intro h; subst k; simp only [Int.natAbs_zero] at hk; omega
    have he : ((realMeanZeroHalfFourierEquiv 2).symm
        (hillRealSignedMap (originalHillRealMeanZeroSource q))).val.val.val k = a.val k := by
      rw [realMeanZeroHalfFourierEquiv_symm_apply,signedOrderHalfFourierEquiv_symm_apply,hz,
        hillRealSignedMap_coordinate,originalHillRealMeanZeroSource_inclusion]
    have hgap : ‖originalCanonicalGapValues q k‖ ≤ 3*‖a.val k‖ := by
      have h := hbound k hk
      rw [he] at h
      change ‖((hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
        (2*k.natAbs)-hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)
        (2*k.natAbs-1):ℝ):ℂ)‖ ≤ 3*‖a.val k‖ at h
      simpa only [originalCanonicalGapValues,if_neg hk0,originalHillLabels] using h
    rw [norm_mul,norm_mul]
    calc
      _ ≤ ‖(Weight.signedSobolev s k:ℂ)‖*(3*‖a.val k‖) :=
        mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
      _ = _ := by ring
  apply hg.mono'
  intro k
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev s).positive k),abs_of_pos ((Weight.signedSobolev s).positive k)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change (1+|(k:ℝ)|)^s ≤ (max 1 |(k:ℝ)|)^s
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)) hs

end NLS.Articles.KdVPseudomeasures
