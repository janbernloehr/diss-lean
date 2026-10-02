import NLS.ZakharovShabat.ClassicalFirstBorn

/-! # Inverse-frequency decay of the first Born term

The bound is exponentially normalized in the spectral imaginary part.
The potential budget consists of its two endpoint values and the
integral of its derivative, separately for each component. This is
the integration-by-parts part of Lemma G.2, before the Sobolev bound
and the Volterra estimate for the full fundamental-solution error.
-/

noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Endpoint and derivative data controlling one oscillatory integral. -/
def classicalOscillatoryVariation (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖f 0‖+‖f t‖+∫ s in (0 : ℝ)..t, ‖deriv f s‖

theorem classicalOscillatoryVariation_nonneg (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ classicalOscillatoryVariation f t :=
  add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (intervalIntegral.integral_nonneg ht (fun _ _ => norm_nonneg _))

/-- The component maximum matches the norm on the classical vector space. -/
def classicalFirstBornBudget (φ : Curve (ℂ × ℂ)) (t : ℝ) : ℝ :=
  max (classicalOscillatoryVariation (fun s => (extend φ s).1) t)
    (classicalOscillatoryVariation (fun s => (extend φ s).2) t)

theorem classicalFirstBornBudget_nonneg (φ : Curve (ℂ × ℂ)) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ classicalFirstBornBudget φ t :=
  (classicalOscillatoryVariation_nonneg _ t ht).trans (le_max_left _ _)

/-- The normalized first Born correction decays as `1/(2*|z|)`.
The hypotheses allow absolutely continuous, not just smooth, potentials. -/
theorem norm_classicalFirstBornVector_weighted_le
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 t)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 t)
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 t)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 t) :
    Real.exp (-(|z.im| * t))*‖classicalFirstBornVector φ z v t‖ ≤
      classicalFirstBornBudget φ t*‖v‖/(2*‖z‖) := by
  have hminus :
      Real.exp (-(|z.im| * t))*‖oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1)‖ ≤
        classicalOscillatoryVariation (fun s => (extend φ s).1) t/(2*‖z‖) := by
    simpa [classicalOscillatoryVariation,Complex.mul_re] using
      norm_oscillatoryIntegral_weighted_le (-I*z) (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz) t ht _ hf hfi
  have hplus :
      Real.exp (-(|z.im| * t))*‖oscillatoryIntegral (I*z) t (fun s => (extend φ s).2)‖ ≤
        classicalOscillatoryVariation (fun s => (extend φ s).2) t/(2*‖z‖) := by
    simpa [classicalOscillatoryVariation,Complex.mul_re] using
      norm_oscillatoryIntegral_weighted_le (I*z) (mul_ne_zero I_ne_zero hz) t ht _ hg hgi
  let E := Real.exp (-(|z.im| * t))
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hB := classicalFirstBornBudget_nonneg φ t ht
  have hbound (a : ℂ) (A : ℝ) (hA : A ≤ classicalFirstBornBudget φ t)
      (ha : E*‖a‖ ≤ A/(2*‖z‖)) (b : ℂ) (hb : ‖b‖ ≤ ‖v‖) :
      E*(‖a‖*‖b‖) ≤ classicalFirstBornBudget φ t*‖v‖/(2*‖z‖) := by
    calc
      _ = (E*‖a‖)*‖b‖ := by ring
      _ ≤ (A/(2*‖z‖))*‖b‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ (classicalFirstBornBudget φ t/(2*‖z‖))*‖v‖ :=
        mul_le_mul (div_le_div_of_nonneg_right hA (by positivity)) hb
          (norm_nonneg _) (div_nonneg hB (by positivity))
      _ = _ := by ring
  change E*‖classicalFirstBornVector φ z v t‖ ≤ _
  rw [classicalFirstBornVector,Prod.norm_def,mul_max_of_nonneg _ _ hE]
  apply max_le
  · simpa only [norm_mul,norm_I,one_mul] using
      hbound _ _ (le_max_left _ _) hminus v.2 (norm_snd_le v)
  · simpa only [norm_mul,norm_neg,norm_I,one_mul] using
      hbound _ _ (le_max_right _ _) hplus v.1 (norm_fst_le v)

/-- A spectral-parameter-independent budget uniform on the unit interval. -/
def classicalFirstBornUniformBudget (φ : Curve (ℂ × ℂ)) : ℝ :=
  2*‖φ‖+max (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).1) s‖)
    (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).2) s‖)

/-- Endpoint evaluation and interval monotonicity turn the local
variation budget into a uniform bound on the full physical interval. -/
theorem classicalFirstBornBudget_le_uniform (φ : Curve (ℂ × ℂ))
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 1)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 1)
    (t : Icc (0 : ℝ) 1) :
    classicalFirstBornBudget φ t ≤ classicalFirstBornUniformBudget φ := by
  have hnorm (s : ℝ) : ‖extend φ s‖ ≤ ‖φ‖ := φ.norm_coe_le_norm _
  have hfst := intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
    (Filter.Eventually.of_forall (fun s => norm_nonneg (deriv (fun x => (extend φ x).1) s))) hfi.norm
  have hsnd := intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
    (Filter.Eventually.of_forall (fun s => norm_nonneg (deriv (fun x => (extend φ x).2) s))) hgi.norm
  apply max_le
  · have h0 := (norm_fst_le (extend φ 0)).trans (hnorm 0)
    have ht := (norm_fst_le (extend φ t)).trans (hnorm t)
    have hmax := le_max_left (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).1) s‖)
      (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).2) s‖)
    dsimp only [classicalOscillatoryVariation,classicalFirstBornUniformBudget]
    linarith
  · have h0 := (norm_snd_le (extend φ 0)).trans (hnorm 0)
    have ht := (norm_snd_le (extend φ t)).trans (hnorm t)
    have hmax := le_max_right (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).1) s‖)
      (∫ s in (0 : ℝ)..1, ‖deriv (fun x => (extend φ x).2) s‖)
    dsimp only [classicalOscillatoryVariation,classicalFirstBornUniformBudget]
    linarith

/-- The exponentially normalized first Born estimate is uniform in
time on `[0,1]` and applies to every nonzero complex spectral parameter. -/
theorem norm_classicalFirstBornVector_weighted_uniform_le
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 1)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 1)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*‖classicalFirstBornVector φ z v t‖ ≤
      classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖) := by
  have hsub : uIcc 0 t.val ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  exact (norm_classicalFirstBornVector_weighted_le φ z hz v t t.property.1
    (hf.mono hsub) (hg.mono hsub) (hfi.mono_set hsub) (hgi.mono_set hsub)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (classicalFirstBornBudget_le_uniform φ hfi hgi t) (norm_nonneg _)) (by positivity))

end NLS.ZakharovShabat
