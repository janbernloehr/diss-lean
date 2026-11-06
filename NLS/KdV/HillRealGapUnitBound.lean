import NLS.KdV.HillL2GapSquareIdentification

/-! # A real action bound from the actual filled gap square -/

noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- The continuous filled square converts an inverse-index unit bound
into a quadratic gap bound for the actual real action. -/
theorem HillL2NormalizedCutPrimitive.gapIntegral_le_of_unit_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8 * ‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ) (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (H : ℂ → ℂ)
    (hfactor : ∀ x ∈ Ioo p.left p.right,
      hillL2CutPrimitiveSquare n p.left p.right F x =
        ((x : ℂ) - p.left) * ((x : ℂ) - p.right) * H x ^ 2)
    (hH : ∀ x ∈ Ioo p.left p.right, ‖H x‖ ≤ 1 / (n : ℝ)) :
    (n : ℝ) * hillRealGapIntegral q hq hr n 0 ≤ (p.right - p.left) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hγ : 0 ≤ p.right - p.left := sub_nonneg.mpr p.ordered
  obtain ⟨p', hl, hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hp := p.endpoints_unique _ n (by omega) p'
  have hl' := hl.trans hp.1.symm
  have hu' := hu.trans hp.2.symm
  have hnonneg (x : ℝ) (hx : x ∈ Icc p.left p.right) :
      0 ≤ hillRealGapProfile (SpectralWeight.one.toCoeff q) n x := by
    apply hillRealGapProfile_nonneg q hq hr n (by omega)
    simpa only [hl', hu'] using hx
  have hends := hillRealGapProfile_endpoints q hq hr n (by omega)
  rw [hl', hu'] at hends
  have hbound (x : ℝ) (hx : x ∈ Icc p.left p.right) :
      hillRealGapProfile (SpectralWeight.one.toCoeff q) n x ≤ (p.right - p.left) / (n : ℝ) := by
    by_cases hxl : x = p.left
    · simpa only [hxl, hends.1] using div_nonneg hγ hnpos.le
    by_cases hxu : x = p.right
    · simpa only [hxu, hends.2] using div_nonneg hγ hnpos.le
    have hxi : x ∈ Ioo p.left p.right :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxu⟩
    have hsq := (h.square_gap_profile q hq hr n hn hcut p hopen R F x hxi).2
    have hnorm : (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x) ^ 2 =
        ‖hillL2CutPrimitiveSquare n p.left p.right F x‖ := by
      rw [hsq, norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hlb : ‖(x : ℂ) - p.left‖ ≤ p.right - p.left := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    have hub : ‖(x : ℂ) - p.right‖ ≤ p.right - p.left := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hx.2)]
      linarith [hx.1]
    have hnormle : ‖hillL2CutPrimitiveSquare n p.left p.right F x‖ ≤
        ((p.right - p.left) / (n : ℝ)) ^ 2 := by
      rw [hfactor x hxi, norm_mul, norm_mul, norm_pow]
      calc
        _ ≤ ((p.right - p.left) * (p.right - p.left)) * (1 / (n : ℝ)) ^ 2 :=
          mul_le_mul (mul_le_mul hlb hub (norm_nonneg _) hγ)
            (pow_le_pow_left₀ (norm_nonneg _) (hH x hxi) 2) (by positivity) (by positivity)
        _ = _ := by ring
    exact (sq_le_sq₀ (hnonneg x hx) (div_nonneg hγ hnpos.le)).mp (hnorm ▸ hnormle)
  have hcont := continuousOn_hillRealGapProfile q hq hr n (by omega)
  rw [hl', hu'] at hcont
  have hi := intervalIntegral.integral_mono_on (μ := volume) p.ordered
    (hcont.intervalIntegrable_of_Icc p.ordered)
    (intervalIntegrable_const (c := (p.right - p.left) / (n : ℝ))) hbound
  have hcoef : 0 ≤ 2 / Real.pi ∧ 2 / Real.pi ≤ 1 :=
    ⟨by positivity, (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hI : hillRealGapIntegral q hq hr n 0 ≤ (p.right - p.left) ^ 2 / (n : ℝ) := by
    unfold hillRealGapIntegral
    rw [hl', hu']
    simp only [pow_zero, one_mul]
    calc
      _ ≤ (2 / Real.pi) * ((p.right - p.left) * ((p.right - p.left) / (n : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hcoef.1
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
      _ ≤ (p.right - p.left) * ((p.right - p.left) / (n : ℝ)) :=
        mul_le_of_le_one_left (mul_nonneg hγ (div_nonneg hγ hnpos.le)) hcoef.2
      _ = _ := by ring
  simpa only [mul_comm] using (le_div_iff₀ hnpos).mp hI

end NLS.KdV
