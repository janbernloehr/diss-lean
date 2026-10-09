import NLS.ZakharovShabat.PhysicalL2IntegralPairing

/-! # Uniformly continuous L2 primitives

Integrating an L2 representative against a fixed bounded continuous function
gives a continuous curve. The construction is a bounded complex-linear map
into the uniform norm, with no pointwise convergence assumption.
-/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Restriction to a shorter physical interval does not increase the L2 norm. -/
theorem norm_intervalL2Restriction_le (t : Icc (0:ℝ) 1) : ‖intervalL2Restriction t‖ ≤ 1 := by
  simpa only [intervalL2Restriction,ENNReal.toReal_one,Real.one_rpow] using
    Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) (c := 1) (by simp)
      (show volume.restrict (Ioc 0 t.val) ≤ (1:ENNReal) • volume.restrict (Ioc 0 1) by
        simpa using Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))

/-- A uniform Cauchy-Schwarz bound for the actual scalar integral. -/
theorem norm_intervalL2_integral_mul_le (u : IntervalL2) (f : ℝ →ᵇ ℂ) (t : Icc (0:ℝ) 1) :
    ‖∫ s in (0:ℝ)..t.val, u s*f s‖ ≤ ‖u‖*‖f‖ := by
  let μ := volume.restrict (Ioc (0:ℝ) t.val)
  let g := (Complex.conjCLE.toContinuousLinearMap.compLeftContinuousBounded ℝ) f
  have hm : (measureUnivNNReal μ : ℝ) ≤ 1 := by
    have hm' : measureUnivNNReal μ ≤ 1 := by
      unfold measureUnivNNReal μ
      rw [Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]
      exact (ENNReal.toNNReal_mono (by simp) (show ENNReal.ofReal t.val ≤ 1 by
        exact_mod_cast (ENNReal.ofReal_le_ofReal t.property.2))).trans_eq (by simp)
    exact_mod_cast hm'
  have hb : ‖BoundedContinuousFunction.toLp 2 μ ℂ g‖ ≤ ‖f‖ := by
    apply (Lp.norm_le_of_ae_bound (norm_nonneg f) ?_).trans
      ((mul_le_mul_of_nonneg_right (Real.rpow_le_one (by positivity) hm (by positivity))
        (norm_nonneg f)).trans_eq (one_mul _))
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ ℂ g] with s hs
    rw [hs]
    simpa [g] using f.norm_coe_le_norm s
  rw [intervalL2_integral_mul_eq_inner]
  apply (norm_inner_le_norm _ _).trans
  have hr := (intervalL2Restriction t).le_opNorm u
  have hr' : ‖intervalL2Restriction t u‖ ≤ ‖u‖ :=
    hr.trans ((mul_le_mul_of_nonneg_right (norm_intervalL2Restriction_le t) (norm_nonneg u)).trans_eq (one_mul _))
  exact (mul_le_mul hb hr' (norm_nonneg _) (norm_nonneg f)).trans_eq (mul_comm _ _)

/-- The actual primitive, continuous up to both endpoints. -/
def intervalL2Primitive (f : ℝ →ᵇ ℂ) (u : IntervalL2) : Curve ℂ where
  toFun t := ∫ s in (0:ℝ)..t.val, u s*f s
  continuous_toFun := by
    have h := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_intervalL2_mul u f ⟨1,by constructor <;> norm_num⟩)
      (show (0:ℝ) ∈ uIcc 0 1 by simp)
    exact h.comp_continuous continuous_subtype_val
      (fun t => by simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using t.property)

@[simp] theorem intervalL2Primitive_apply (f : ℝ →ᵇ ℂ) (u : IntervalL2) (t : Icc (0:ℝ) 1) :
    intervalL2Primitive f u t = ∫ s in (0:ℝ)..t.val, u s*f s := rfl

/-- Primitive convergence is uniform in time under L2 convergence of the input. -/
def intervalL2PrimitiveCLM (f : ℝ →ᵇ ℂ) : IntervalL2 →L[ℂ] Curve ℂ :=
  LinearMap.mkContinuous
    { toFun := intervalL2Primitive f
      map_add' := by
        intro u v
        apply ContinuousMap.ext
        intro t
        change (∫ s in (0:ℝ)..t.val, (u+v) s*f s) =
          (∫ s in (0:ℝ)..t.val, u s*f s)+(∫ s in (0:ℝ)..t.val, v s*f s)
        rw [← intervalIntegral.integral_add (intervalIntegrable_intervalL2_mul u f t)
          (intervalIntegrable_intervalL2_mul v f t)]
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le t.property.1]
        filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
          (Lp.coeFn_add u v)] with s hs
        simp only [hs,Pi.add_apply,add_mul]
      map_smul' := by
        intro c u
        apply ContinuousMap.ext
        intro t
        change (∫ s in (0:ℝ)..t.val, (c • u) s*f s) = c • (∫ s in (0:ℝ)..t.val, u s*f s)
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le t.property.1]
        filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
          (Lp.coeFn_smul c u)] with s hs
        simp only [hs,Pi.smul_apply,smul_eq_mul,mul_assoc] }
    ‖f‖ (by
      intro u
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg f) (norm_nonneg u))).mpr
      intro t
      exact (norm_intervalL2_integral_mul_le u f t).trans_eq (mul_comm _ _))

@[simp] theorem intervalL2PrimitiveCLM_apply (f : ℝ →ᵇ ℂ) (u : IntervalL2) (t : Icc (0:ℝ) 1) :
    intervalL2PrimitiveCLM f u t = ∫ s in (0:ℝ)..t.val, u s*f s := rfl

end NLS.ZakharovShabat
