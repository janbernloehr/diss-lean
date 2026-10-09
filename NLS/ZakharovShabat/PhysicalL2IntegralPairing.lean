import NLS.ZakharovShabat.ContinuousPotentialL2Class

/-! # Continuity of actual L2 integral pairings on truncated intervals

The integral is the ordinary Bochner integral of representatives. Its joint
continuity follows from its exact identification with an L2 inner product;
no pointwise convergence of L2 representatives is assumed.
-/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Extend a continuous curve by endpoint values, as a bounded continuous function. -/
def curveBoundedExtension (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Curve E →L[ℂ] (ℝ →ᵇ E) :=
  (BoundedContinuousFunction.compContinuousCLM E ℂ
    ⟨projIcc 0 1 (by norm_num),continuous_projIcc⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0:ℝ) 1) E ℂ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem curveBoundedExtension_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : Curve E) (s : ℝ) : curveBoundedExtension E w s = extend w s := rfl

/-- Restrict a physical scalar L2 class to a shorter interval. -/
def intervalL2Restriction (t : Icc (0:ℝ) 1) :
    IntervalL2 →L[ℝ] Lp ℂ 2 (volume.restrict (Ioc 0 t.val)) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))

theorem intervalL2Restriction_representative (u : IntervalL2) (t : Icc (0:ℝ) 1) :
    intervalL2Restriction t u =ᵐ[volume.restrict (Ioc 0 t.val)] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

/-- The actual scalar integral is an L2 inner product with the conjugate test function. -/
theorem intervalL2_integral_mul_eq_inner (u : IntervalL2) (f : ℝ →ᵇ ℂ) (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, u s*f s) =
      inner ℂ (BoundedContinuousFunction.toLp 2 (volume.restrict (Ioc 0 t.val)) ℂ
        ((Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ℝ) f))
        (intervalL2Restriction t u) := by
  rw [L2.inner_def,intervalIntegral.integral_of_le t.property.1]
  apply integral_congr_ae
  filter_upwards [intervalL2Restriction_representative u t,
    BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Ioc 0 t.val)) ℂ
      ((Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ℝ) f)] with s hu hf
  rw [hu,hf,RCLike.inner_apply]
  simp

/-- Joint continuity of the original scalar integral, with the L2 and uniform norms. -/
theorem continuous_intervalL2_integral_mul (t : Icc (0:ℝ) 1) :
    Continuous (fun p : IntervalL2 × (ℝ →ᵇ ℂ) => ∫ s in (0:ℝ)..t.val, p.1 s*p.2 s) := by
  simp_rw [intervalL2_integral_mul_eq_inner]
  exact ((BoundedContinuousFunction.toLp 2 (volume.restrict (Ioc 0 t.val)) ℂ).continuous.comp
    ((Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ℝ).continuous.comp continuous_snd)).inner
    ((intervalL2Restriction t).continuous.comp continuous_fst)

/-- Products of a physical L2 representative and a bounded continuous test function are integrable. -/
theorem intervalIntegrable_intervalL2_mul (u : IntervalL2) (f : ℝ →ᵇ ℂ) (t : Icc (0:ℝ) 1) :
    IntervalIntegrable (fun s => u s*f s) volume 0 t.val := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le t.property.1).mpr
  have hu : MemLp u 2 (volume.restrict (Ioc (0:ℝ) t.val)) :=
    (Lp.memLp u).mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
  exact MemLp.integrable (by norm_num : 1 ≤ (2:ENNReal)) (f.memLp_top.mul hu)

/-- Integration on a truncated interval is continuous in the uniform norm. -/
theorem continuous_bounded_intervalIntegral (t : Icc (0:ℝ) 1) :
    Continuous (fun f : ℝ →ᵇ ℂ => ∫ s in (0:ℝ)..t.val, f s) := by
  let oneClass : IntervalL2 := BoundedContinuousFunction.toLp 2 (volume.restrict (Ioc 0 1)) ℂ 1
  have h : Continuous (fun f : ℝ →ᵇ ℂ => ∫ s in (0:ℝ)..t.val, oneClass s*f s) :=
    (continuous_intervalL2_integral_mul t).comp (continuous_const.prodMk continuous_id)
  convert h using 1
  ext f
  apply intervalIntegral.integral_congr_ae_restrict
  have he := ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Ioc 0 1)) ℂ (1 : ℝ →ᵇ ℂ))
  rw [uIoc_of_le t.property.1]
  filter_upwards [he] with s hs
  simp only [oneClass] at *
  rw [hs]
  simp

end NLS.ZakharovShabat
