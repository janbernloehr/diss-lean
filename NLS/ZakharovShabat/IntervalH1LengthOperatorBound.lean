import NLS.ComplexAnalysis.IntervalH1LengthBound
import NLS.ZakharovShabat.IntervalH1OperatorBound

/-! # An arbitrary-interval Born bound in the explicit integral H1 norm

The coefficient records the interval length. This is a norm-qualified
replacement candidate, not an identification of the printed G.2 local norm.
-/
noncomputable section
open Set MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem norm_oscillatoryIntegral_weighted_le_interval_H1
    (T : ℝ) (hT : 0 < T) (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hL2 : MemLp f 2 (volume.restrict (Ioc 0 T)))
    (hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc 0 T)))
    (t : Icc (0 : ℝ) T) :
    Real.exp (-(|c.re| * t.val))*‖oscillatoryIntegral c t f‖ ≤
      Real.sqrt (T⁻¹+T)/‖c‖*intervalH1Norm f T := by
  have hsub : uIcc 0 t.val ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le t.property.1,uIcc_of_le hT.le]
    exact Icc_subset_Icc le_rfl t.property.2
  have hi : IntervalIntegrable (deriv f) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hdL2.integrable (by norm_num))
  apply (norm_oscillatoryIntegral_weighted_le c hc t t.property.1 f (hf.mono hsub)
    (hi.mono_set hsub)).trans
  exact (div_le_div_of_nonneg_right (endpoint_variation_le_length_H1 f T hT hf hL2 hdL2 t)
    (by positivity)).trans_eq (by ring)

/-- The uniform Born estimate for genuine interval H1 inputs. The constant
comes from the combined trace estimate, not a constant-one trace embedding. -/
theorem intervalHermitianFirstBornOperator_weighted_le_interval_H1
    (T : ℝ) (hT : 0 < T) (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 T)))
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 T)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 T)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 T)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 T)))
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) T) :
    Real.exp (-(|z.im| * t.val))*‖intervalHermitianFirstBornOperator φ z t‖ ≤
      Real.sqrt (T⁻¹+T)/‖z‖*intervalPairH1Norm φ T := by
  have hminus := norm_oscillatoryIntegral_weighted_le_interval_H1 T hT (-Complex.I*z)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz) _ hf hφ.fst hdf t
  have hplus := norm_oscillatoryIntegral_weighted_le_interval_H1 T hT (Complex.I*z)
    (mul_ne_zero Complex.I_ne_zero hz) _ hg hφ.snd hdg t
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_one_mul,zero_sub,neg_neg,one_mul,
    abs_neg,norm_mul,norm_neg,Complex.norm_I] at hminus hplus
  rw [norm_intervalHermitianFirstBornOperator,mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  exact max_le (hminus.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_fst_le_pair φ T)
    (by positivity))) (hplus.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_snd_le_pair φ T)
    (by positivity)))


/-- The bound in the local integral norm on [0,t] for every nonnegative t.
The zero-length case is the zero operator. -/
theorem intervalHermitianFirstBornOperator_weighted_le_local_H1
    (t : ℝ) (ht : 0 ≤ t) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 t)))
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 t)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 t)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 t)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 t)))
    (z : ℂ) (hz : z ≠ 0) :
    Real.exp (-(|z.im| * t))*‖intervalHermitianFirstBornOperator φ z t‖ ≤
      Real.sqrt (t⁻¹+t)/‖z‖*intervalPairH1Norm φ t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    simp [norm_intervalHermitianFirstBornOperator,oscillatoryIntegral]
  · exact intervalHermitianFirstBornOperator_weighted_le_interval_H1 t ht φ hφ hf hg hdf hdg z hz ⟨t,ht.le,le_rfl⟩

/-- After removing the necessary inverse-square-root length factor, the
coefficient is exactly sqrt(1+t^2), tending to one as t tends to zero. -/
theorem intervalH1_length_factor_normalized (t : ℝ) (ht : 0 < t) :
    Real.sqrt (t⁻¹+t)*Real.sqrt t = Real.sqrt (1+t^2) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ t⁻¹+t)]
  congr 1
  rw [add_mul,inv_mul_cancel₀ ht.ne']
  ring

/-- The sufficient numerator divided by the necessary 2/sqrt(t) tends to
one at short positive times. Thus the leading small-time constant is sharp. -/
theorem tendsto_intervalH1_length_factor_normalized :
    Filter.Tendsto (fun t : ℝ => Real.sqrt (t⁻¹+t)*Real.sqrt t)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (1+t^2)) :=
    (continuous_const.add (continuous_id.pow 2)).sqrt
  have hl : Filter.Tendsto (fun t : ℝ => Real.sqrt (1+t^2))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (intervalH1_length_factor_normalized t ht).symm

end NLS.ZakharovShabat
