import NLS.ComplexAnalysis.AppendixGBornDerivative
import NLS.ZakharovShabat.IntervalH1LengthOperatorBound
import NLS.ZakharovShabat.ClassicalHermitianTimeBounds
import NLS.ZakharovShabat.SourcePeriodicH1Norm

/-! # Positive Appendix G Born-derivative bounds in the physical operator norm

The derivative is the actual time derivative of the first Born operator.
The arbitrary interval bound uses the explicit integral H1 norm. The
period-one specialization uses the original Chapter 5 source norm.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The exact integration-by-parts identity for the physical Born operator.
The signs follow the original free modes and potential components. -/
theorem appendixG_Born_operator_parts
    (φ : ℝ → ℂ × ℂ) (z : ℂ) (t : ℝ)
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 t)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 t)
    (hdf : IntervalIntegrable (deriv (fun s => (φ s).1)) volume 0 t)
    (hdg : IntervalIntegrable (deriv (fun s => (φ s).2)) volume 0 t) :
    (2*z) • intervalHermitianFirstBornOperator φ z t =
      hermitianColumns
        (0,exp (-I*z*t)*(φ t).2-exp (I*z*t)*(φ 0).2-
          oscillatoryIntegral (I*z) t (deriv (fun s => (φ s).2)))
        (exp (I*z*t)*(φ t).1-exp (-I*z*t)*(φ 0).1-
          oscillatoryIntegral (-I*z) t (deriv (fun s => (φ s).1)),0) := by
  have hm := oscillatoryIntegral_parts (-I*z) t (fun s => (φ s).1) hf hdf
  have hp := oscillatoryIntegral_parts (I*z) t (fun s => (φ s).2) hg hdg
  rw [intervalHermitianFirstBornOperator,← hermitianColumnsCLM_apply
    ((0,-I*oscillatoryIntegral (I*z) t (fun s => (φ s).2)),
      (I*oscillatoryIntegral (-I*z) t (fun s => (φ s).1),0)),
    ← map_smul,hermitianColumnsCLM_apply]
  congr 1
  · apply Prod.ext
    · simp
    · simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      simp only [neg_mul] at hp ⊢
      linear_combination -hp
  · apply Prod.ext
    · simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      simp only [neg_mul,neg_neg] at hm ⊢
      linear_combination -hm
    · simp

/-- Differentiate the genuine Born operator through its two columns. -/
theorem appendixG_deriv_intervalHermitianFirstBornOperator
    (φ : ℝ → ℂ × ℂ) (hφ : Continuous φ) (z : ℂ) (t : ℝ) :
    deriv (intervalHermitianFirstBornOperator φ z) t =
      hermitianColumns
        (0,-I*deriv (fun u => oscillatoryIntegral (I*z) u (fun s => (φ s).2)) t)
        (I*deriv (fun u => oscillatoryIntegral (-I*z) u (fun s => (φ s).1)) t,0) := by
  change deriv (fun u => hermitianColumns
    (0,-I*oscillatoryIntegral (I*z) u (fun s => (φ s).2))
    (I*oscillatoryIntegral (-I*z) u (fun s => (φ s).1),0)) t = _
  have hm := (appendixG_hasDerivAt_oscillatoryIntegral (-I*z) _ hφ.fst t).differentiableAt.hasDerivAt
  have hp := (appendixG_hasDerivAt_oscillatoryIntegral (I*z) _ hφ.snd t).differentiableAt.hasDerivAt
  have hu := (hasDerivAt_const t (0 : ℂ)).prodMk (hp.const_mul (-I))
  have hv := (hm.const_mul I).prodMk (hasDerivAt_const t (0 : ℂ))
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
    hermitianColumnsCLM_apply,intervalHermitianFirstBornOperator] using
    ((hermitianColumnsCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hu.prodMk hv)).deriv

/-- The Hermitian operator norm is exactly the larger scalar derivative norm. -/
theorem appendixG_norm_deriv_intervalHermitianFirstBornOperator
    (φ : ℝ → ℂ × ℂ) (hφ : Continuous φ) (z : ℂ) (t : ℝ) :
    ‖deriv (intervalHermitianFirstBornOperator φ z) t‖ =
      max ‖deriv (fun u => oscillatoryIntegral (-I*z) u (fun s => (φ s).1)) t‖
        ‖deriv (fun u => oscillatoryIntegral (I*z) u (fun s => (φ s).2)) t‖ := by
  rw [appendixG_deriv_intervalHermitianFirstBornOperator φ hφ z t,
    norm_hermitianColumns_offDiagonal]
  simp only [norm_mul,norm_neg,norm_I,one_mul]

/-- A positive length-dependent bound for the actual derivative, including
zero spectral parameter and both endpoints of the time interval. -/
theorem appendixG_Born_derivative_interval_H1
    (T : ℝ) (hT : 0 < T) (φ : ℝ → ℂ × ℂ) (hc : Continuous φ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 T)))
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 T)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 T)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 T)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 T)))
    (z : ℂ) (t : Icc (0 : ℝ) T) :
    Real.exp (-(|z.im| * t.val))*‖deriv (intervalHermitianFirstBornOperator φ z) t‖ ≤
      Real.sqrt (T⁻¹+T)*intervalPairH1Norm φ T := by
  have hm := appendixG_oscillatoryIntegral_derivative_interval_H1 T hT (-I*z)
    _ hc.fst hf hφ.fst hdf t
  have hp := appendixG_oscillatoryIntegral_derivative_interval_H1 T hT (I*z)
    _ hc.snd hg hφ.snd hdg t
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_one_mul,zero_sub,neg_neg,one_mul,abs_neg] at hm hp
  rw [appendixG_norm_deriv_intervalHermitianFirstBornOperator φ hc z t,
    mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  exact max_le (hm.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_fst_le_pair φ T)
    (by positivity))) (hp.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_snd_le_pair φ T)
    (by positivity)))

/-- The original periodic source norm gives a uniform sqrt(2) bound
throughout the closed unit interval, at every complex spectral parameter. -/
theorem appendixG_source_Born_derivative_unit
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*
      ‖deriv (intervalHermitianFirstBornOperator (sourcePeriodicH1Potential a) z) t‖ ≤
      Real.sqrt 2*‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  have h := appendixG_Born_derivative_interval_H1 1 (by norm_num)
    (sourcePeriodicH1Potential a) (continuous_sourcePeriodicH1Potential a)
    (memLp_sourcePeriodicH1Potential a)
    (NLS.Fourier.absolutelyContinuous_periodOneSobolevSynthesis a.1)
    (NLS.Fourier.absolutelyContinuous_periodOneSobolevSynthesis a.2)
    (NLS.Fourier.memLp_deriv_periodOneSobolevSynthesis a.1)
    (NLS.Fourier.memLp_deriv_periodOneSobolevSynthesis a.2) z t
  norm_num only [inv_one,one_add_one_eq_two] at h
  exact h.trans (mul_le_mul_of_nonneg_left (intervalPairH1Norm_sourcePeriodic_le a)
    (Real.sqrt_nonneg _))

end NLS.ZakharovShabat
