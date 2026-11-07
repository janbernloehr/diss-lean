import NLS.KdV.HillEndpointResonantBounds

/-! Both signed resonant errors of the ACTUAL endpoint inverse family,
controlled by the SAME source physical L2 norm. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual inverse-minus-identity is small in BOTH original shifted
endpoint norms, with the exact factor TWO from the proved inverse bound. -/
theorem negativeShiftedNorm_endpointInverseFamily_sub_le
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (i : ℤ) (hi : i=(n:ℤ) ∨ i=-(n:ℤ)) :
    SpectralWeight.one.negativeShiftedNorm r hr i ⊤ (endpointInverseFamily r hr hr1 n (q,z) a-a) ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*SpectralWeight.one.negativeShiftedNorm r hr i ⊤ a := by
  rw [endpointInverseFamily_eq r hr hr1 n hn (q,z) hz hs]
  let K := endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
  have hright := endpointHillTailInverse_right SpectralWeight.one r hr hr1 n hn z hz q hs a
  have he : K a-a=unshiftedEndpointHillPerturbation SpectralWeight.one r hr hr1 n hn z hz q (K a) := by
    apply sub_eq_iff_eq_add.mpr
    exact (sub_eq_iff_eq_add.mp hright).trans (add_comm _ _)
  have hK := negativeShiftedNorm_endpointHillTailInverse_le SpectralWeight.one r hr hr1 n hn z hz q hs a
  have hT := negativeShiftedNorm_endpointHillPerturbation_le SpectralWeight.one r hr hr1 n hn z hz q (K a)
  have hk : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
    positivity [endpointHillConstant_pos r hr1]
  change SpectralWeight.one.negativeShiftedNorm r hr i ⊤ (K a-a) ≤ _
  rw [he]
  rcases hi with rfl | rfl
  · exact (hT.1.trans (mul_le_mul_of_nonneg_left hK.1 hk)).trans_eq (by ring)
  · exact (hT.2.trans (mul_le_mul_of_nonneg_left hK.2 hk)).trans_eq (by ring)

/-- The ACTUAL two-mode inverse response differs from the original physical
amplitudes by at most TWO times the genuine perturbation majorant. -/
theorem norm_endpointInverseFamily_coordinates_sub_le_L2
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    ‖hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (endpointInverseFamily r hr hr1 n (q,z) (H1EndpointInclusion r hr f))-endpointHillH1Coordinates n f‖ ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖singularHillL2DomainInclusion f‖ := by
  let a := H1EndpointInclusion r hr f
  let K := endpointInverseFamily r hr hr1 n (q,z)
  have hk : 0 ≤ 2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖) := by
    positivity [endpointHillConstant_pos r hr1]
  have hc (k : ℤ) (hres : -k=(n:ℤ) ∨ -k=-(n:ℤ)) :
      ‖(K a).val k-a.val k‖ ≤ 2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖singularHillL2DomainInclusion f‖ := by
    have hcoord := norm_apply_le_negativeShiftedNorm_one r hr (-k) (K a-a) k
    simp only [add_neg_cancel,Weight.sobolev_apply,Int.cast_zero,abs_zero,add_zero,Real.one_rpow,mul_one] at hcoord
    have hbound := negativeShiftedNorm_endpointInverseFamily_sub_le r hr hr1 n hn z hz q hs a (-k) hres
    exact hcoord.trans (hbound.trans (mul_le_mul_of_nonneg_left
      (negativeShiftedNorm_H1EndpointInclusion_le_L2 r hr f (-k)) hk))
  rw [endpointHillH1Coordinates_apply,hillModeCoordinates_apply]
  change ‖((K a).val (n:ℤ)-f.val (SmoothPeriodicTest.mode (-(n:ℤ))),
    (K a).val (-(n:ℤ))-f.val (SmoothPeriodicTest.mode (n:ℤ)))‖ ≤ _
  rw [Prod.norm_def]
  exact max_le (by simpa only [a,H1EndpointInclusion_apply] using hc (n:ℤ) (Or.inr rfl))
    (by simpa only [a,H1EndpointInclusion_apply,neg_neg] using hc (-(n:ℤ)) (Or.inl (by simp)))

end NLS.KdV
