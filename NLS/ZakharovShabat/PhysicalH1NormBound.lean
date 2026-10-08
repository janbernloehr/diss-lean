import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity

/-! # The Fourier comparison used in Lemma 27.1 -/
noncomputable section
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Physical H¹ coordinates of the original order-one source space. -/
def sourcePhysicalH1Coordinates (a : ScalarDomain 2 × ScalarDomain 2) : CoeffPair 2 :=
  sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)

@[simp] theorem sourcePhysicalH1Coordinates_fst (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sourcePhysicalH1Coordinates a).fst n =
      ((1+|((2*n:ℤ):ℝ)*Real.pi| : ℝ):ℂ)*a.1.val n := by
  rw [sourcePhysicalH1Coordinates, sourcePiSobolevCoordinates_fst]
  have he : (higherSobolevSourceOneEquiv a).1.val n = a.1.val n := one_mul _
  rw [he]
  congr 2
  simp

@[simp] theorem sourcePhysicalH1Coordinates_snd (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sourcePhysicalH1Coordinates a).snd n =
      ((1+|((2*n:ℤ):ℝ)*Real.pi| : ℝ):ℂ)*a.2.val n := by
  rw [sourcePhysicalH1Coordinates, sourcePiSobolevCoordinates_snd]
  have he : (higherSobolevSourceOneEquiv a).2.val n = a.2.val n := one_mul _
  rw [he]
  congr 2
  simp

/-- The discrete nonzero frequencies are large enough for the factor 3/2. -/
theorem physical_H1_weight_sq_le (n : ℤ) :
    (1+|((2*n:ℤ):ℝ)*Real.pi|)^2 ≤ (3/2:ℝ)*(1+(2*Real.pi*(n:ℝ))^2) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  have hnat : 1 ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hlarge : 6 ≤ 2*Real.pi*|(n:ℝ)| := by nlinarith [Real.pi_gt_three]
  have hnon : 0 ≤ 2*Real.pi*|(n:ℝ)| := by positivity
  simp only [Int.cast_mul, Int.cast_ofNat, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_of_pos Real.pi_pos]
  have he : (2*Real.pi*(n:ℝ))^2 = (2*Real.pi*|(n:ℝ)|)^2 := by
    simp only [mul_pow, sq_abs]
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.mpr hlarge) hnon]

private theorem hilbert_norm_sq (b : Coeff 2) : ‖b‖^2 = ∑' n : ℤ, ‖b n‖^2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal) b

private theorem hilbert_sq_summable (b : Coeff 2) : Summable (fun n : ℤ => ‖b n‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp b).summable (by norm_num : 0 < (2:ENNReal).toReal)

/-- Any uniform frequency-weight comparison transfers to the physical scalar norm. -/
theorem sourcePhysicalH1_fst_sq_le_of_weight_bound (a : ScalarDomain 2 × ScalarDomain 2)
    (C : ℝ) (hC : ∀ n : ℤ, (1+|((2*n:ℤ):ℝ)*Real.pi|)^2 ≤
      C*(1+(2*Real.pi*(n:ℝ))^2)) :
    ‖(sourcePhysicalH1Coordinates a).fst‖^2 ≤
      C*(‖scalarInclusion a.1‖^2+‖periodOneDerivative a.1‖^2) := by
  rw [hilbert_norm_sq, hilbert_norm_sq (scalarInclusion a.1), hilbert_norm_sq (periodOneDerivative a.1)]
  have hs := ((hilbert_sq_summable (scalarInclusion a.1)).add
    (hilbert_sq_summable (periodOneDerivative a.1))).mul_left C
  have h := (hilbert_sq_summable (sourcePhysicalH1Coordinates a).fst).tsum_le_tsum (fun n => ?_) hs
  · simpa only [tsum_mul_left, Summable.tsum_add (hilbert_sq_summable (scalarInclusion a.1))
      (hilbert_sq_summable (periodOneDerivative a.1))] using h
  · rw [sourcePhysicalH1Coordinates_fst, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 1+|((2*n:ℤ):ℝ)*Real.pi|), mul_pow,
      scalarInclusion_apply, periodOneDerivative_apply]
    have hb := mul_le_mul_of_nonneg_right (hC n) (sq_nonneg ‖a.1.val n‖)
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_intCast, mul_one] 
    simp only [mul_pow, sq_abs] at hb ⊢
    nlinarith

/-- The first physical H¹ component is controlled with the source's factor 3/2. -/
theorem sourcePhysicalH1_fst_sq_le (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖(sourcePhysicalH1Coordinates a).fst‖^2 ≤
      (3/2:ℝ)*(‖scalarInclusion a.1‖^2+‖periodOneDerivative a.1‖^2) :=
  sourcePhysicalH1_fst_sq_le_of_weight_bound a (3/2) physical_H1_weight_sq_le

/-- Real-type coordinates have equal component norms, preserving the factor two in the energy. -/
theorem sourcePhysicalH1_norm_sq_eq_twice_fst (a : realTypeSobolevSourceLocus) :
    ‖sourcePhysicalH1Coordinates a.val‖^2 = 2*‖(sourcePhysicalH1Coordinates a.val).fst‖^2 := by
  have he : (sourcePhysicalH1Coordinates a.val).snd =
      star (Coeff.reflection (sourcePhysicalH1Coordinates a.val).fst) := by
    ext n
    change _ = conj ((sourcePhysicalH1Coordinates a.val).fst (-n))
    rw [sourcePhysicalH1Coordinates_snd, sourcePhysicalH1Coordinates_fst]
    have hr := a.property n
    change (sobolevSourceInclusion a.val).snd n = conj ((sobolevSourceInclusion a.val).fst (-n)) at hr
    simp only [sobolevSourceInclusion_snd, sobolevSourceInclusion_fst] at hr
    rw [hr]
    simp only [mul_neg, Int.cast_neg, neg_mul, abs_neg, map_mul, Complex.conj_ofReal]
  rw [WithLp.prod_norm_sq_eq_of_L2, he, norm_star, Coeff.reflection.norm_map]
  ring

/-- The physical H¹ norm obeys exactly the comparison printed in Lemma 27.1. -/
theorem sourcePhysicalH1_third_sq_le_mass_kinetic (a : realTypeSobolevSourceLocus) :
    (1/3:ℝ)*‖sourcePhysicalH1Coordinates a.val‖^2 ≤
      (periodOneSobolevMass a.val).re+(periodOneSobolevKinetic a.val).re := by
  rw [periodOneSobolevMass_real_eq, periodOneSobolevKinetic_real_eq, Complex.ofReal_re,
    Complex.ofReal_re, sourcePhysicalH1_norm_sq_eq_twice_fst]
  linarith [sourcePhysicalH1_fst_sq_le a.val]

end NLS.ZakharovShabat
