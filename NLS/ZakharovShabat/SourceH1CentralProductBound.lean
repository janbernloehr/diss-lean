import NLS.ZakharovShabat.SourceRealCentralProduct
import NLS.ZakharovShabat.H1CutoffCentralStrip

/-! # The finite central product in Lemma 28.1 on real H¹ sources

The squared-norm estimate keeps the boundary indices ±N and uses both
spectral directions without any reflection assumption on the source.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Localization of a complex point controls the absolute value of its real part. -/
theorem localized_point_abs_re_lower (z : ℂ) (n : ℤ)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5) :
    Real.pi*|(n:ℝ)|-Real.pi/5 ≤ |z.re| := by
  have h := (Complex.abs_re_le_norm (z-(Real.pi:ℂ)*n)).trans hz
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.intCast_re,
    Complex.ofReal_im,zero_mul,sub_zero] at h
  have ht := abs_add_le (Real.pi*n-z.re) z.re
  rw [sub_add_cancel,abs_sub_comm (Real.pi*n) z.re,abs_mul,abs_of_pos Real.pi_pos] at ht
  linarith

/-- The enclosing-interval ratio is controlled even at the boundary index. -/
theorem central_enclosing_ratio_le_eight (N x : ℝ) (hN : 1 ≤ N)
    (hx : Real.pi*(N-1/5) ≤ x) :
    (x+(N-1/2)*Real.pi)/(x-(N-1/2)*Real.pi) ≤ 8*(N+1) := by
  have hd : 0 < x-(N-1/2)*Real.pi := by nlinarith [Real.pi_pos]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_nonneg (by linarith : 0 ≤ 8*N+7) (sub_nonneg.mpr hx)
  nlinarith [Real.pi_pos,mul_nonneg (by linarith : 0 ≤ N) Real.pi_pos.le]

/-- The squared norm of the actual central product has an inclusive cutoff bound. -/
theorem sourceH1_real_central_product_sq_le (ψ : realTypeSourceSubmodule 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ.val)
    (N : ℕ) (hNpos : 1 ≤ N) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ))
    (n : ℤ) (hn : N ≤ n.natAbs) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
      (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
        (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖^2 ≤
      8*((N:ℝ)+1) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ.val
  have hb (m : ℤ) (hm : m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ)) :=
    H1_canonicalEndpoints_cutoff_central_re φ heven N hN m (by simp only [Finset.mem_Ioo] at hm; omega)
  simp only [hφ] at hb
  have hloc := sourceH1_gap_point_norm_localization ψ.val φ hφ n
    (exterior_index_localization_threshold ‖φ‖ N hN n hn) z hz
  have hlow := localized_point_abs_re_lower z n hloc
  have hn' : (N:ℝ) ≤ |(n:ℝ)| := by
    have h : (N:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have hx : Real.pi*((N:ℝ)-1/5) ≤ |z.re| := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn')]
  have h := sourceReal_finite_gap_product_sq_le (by simp) (by norm_num) ψ.val ψ.property
    (Finset.Ioo (-(N:ℤ)) (N:ℤ)) (((N:ℝ)-1/2)*Real.pi)
    (mul_nonneg (by linarith) Real.pi_pos.le) hb z
    (sourcePeriodicSegment_im_eq_zero_of_realType (by simp) (by norm_num) ψ.val ψ.property n z hz)
    (by nlinarith [Real.pi_pos])
  exact h.trans (central_enclosing_ratio_le_eight N |z.re| hN1 hx)

end NLS.ZakharovShabat
