import NLS.ComplexAnalysis.OscillatoryIntegralL2
import NLS.ZakharovShabat.L2HermitianFirstBorn

/-! # The G.2 first Born estimate on arbitrary finite intervals

The matrix uses the original potential functions and the Hermitian induced
operator norm. The estimate retains actual endpoint values and derivative
L2 integrals. The printed H1 norm is not identified with these data here.
-/
noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual first Born operator, without a unit-interval restriction. -/
def intervalHermitianFirstBornOperator (φ : ℝ → ℂ × ℂ) (z : ℂ) (t : ℝ) :
    HermitianPair →L[ℂ] HermitianPair :=
  hermitianColumns ((0 : ℂ),-Complex.I*oscillatoryIntegral (Complex.I*z) t (fun s => (φ s).2))
    (Complex.I*oscillatoryIntegral (-Complex.I*z) t (fun s => (φ s).1),(0 : ℂ))

/-- Exact operator norm; neither a change of vector norm nor a matrix
norm-equivalence constant occurs. -/
theorem norm_intervalHermitianFirstBornOperator (φ : ℝ → ℂ × ℂ) (z : ℂ) (t : ℝ) :
    ‖intervalHermitianFirstBornOperator φ z t‖ =
      max ‖oscillatoryIntegral (-Complex.I*z) t (fun s => (φ s).1)‖
        ‖oscillatoryIntegral (Complex.I*z) t (fun s => (φ s).2)‖ := by
  rw [intervalHermitianFirstBornOperator,norm_hermitianColumns_offDiagonal]
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul]

/-- Exact recovery of the previously constructed continuous-potential operator. -/
theorem intervalHermitianFirstBornOperator_of_continuous
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    intervalHermitianFirstBornOperator (extend φ) z t =
      classicalHermitianFirstBornOperator φ z t := by
  simp [intervalHermitianFirstBornOperator,classicalHermitianFirstBornOperator,
    classicalFirstBornVector]

/-- Exact recovery of the physical L2 operator for every original representative. -/
theorem intervalHermitianFirstBornOperator_eq_l2
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (t : Icc (0 : ℝ) 1) :
    intervalHermitianFirstBornOperator φ z t =
      l2HermitianFirstBornOperatorCurve (intervalL2OfFunction φ hφ) z t := by
  rw [l2HermitianFirstBornOperatorCurve_ofFunction]
  rfl

/-- G.2's integration-by-parts bound for any nonnegative time and any
nonzero complex frequency, with the trace data displayed explicitly. -/
theorem intervalHermitianFirstBornOperator_weighted_le
    (φ : ℝ → ℂ × ℂ) (z : ℂ) (hz : z ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 t)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 t)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 t)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 t))) :
    Real.exp (-(|z.im| * t))*‖intervalHermitianFirstBornOperator φ z t‖ ≤
      (‖φ 0‖+‖φ t‖+Real.sqrt t *
        max (Real.sqrt (∫ s in 0..t, ‖deriv (fun r => (φ r).1) s‖^2))
          (Real.sqrt (∫ s in 0..t, ‖deriv (fun r => (φ r).2) s‖^2)))/(2*‖z‖) := by
  have hminus := norm_oscillatoryIntegral_weighted_le_L2 (-Complex.I*z)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz) t ht _ hf hdf
  have hplus := norm_oscillatoryIntegral_weighted_le_L2 (Complex.I*z)
    (mul_ne_zero Complex.I_ne_zero hz) t ht _ hg hdg
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_one_mul,zero_sub,neg_neg,one_mul,
    abs_neg,norm_mul,norm_neg,Complex.norm_I] at hminus hplus
  rw [norm_intervalHermitianFirstBornOperator,
    mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  apply max_le
  · apply hminus.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (add_le_add (norm_fst_le _) (norm_fst_le _))
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _))
  · apply hplus.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (add_le_add (norm_snd_le _) (norm_snd_le _))
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _))

/-- The exact printed numerical factor under an explicit trace and
L2 derivative bound. Identifying H with the source norm is a separate step. -/
theorem intervalHermitianFirstBornOperator_weighted_le_of_trace_L2_bound
    (φ : ℝ → ℂ × ℂ) (z : ℂ) (hz : z ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 t)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 t)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 t)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 t)))
    (H : ℝ) (h0 : ‖φ 0‖ ≤ H) (htφ : ‖φ t‖ ≤ H)
    (hD : max (Real.sqrt (∫ s in 0..t, ‖deriv (fun r => (φ r).1) s‖^2))
      (Real.sqrt (∫ s in 0..t, ‖deriv (fun r => (φ r).2) s‖^2)) ≤ H) :
    Real.exp (-(|z.im| * t))*‖intervalHermitianFirstBornOperator φ z t‖ ≤
      (2+Real.sqrt t)/(2*‖z‖)*H := by
  apply (intervalHermitianFirstBornOperator_weighted_le φ z hz t ht hf hg hdf hdg).trans
  calc
    _ ≤ (H+H+Real.sqrt t*H)/(2*‖z‖) :=
      div_le_div_of_nonneg_right (add_le_add (add_le_add h0 htφ)
        (mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _))) (by positivity)
    _ = _ := by ring

end NLS.ZakharovShabat
