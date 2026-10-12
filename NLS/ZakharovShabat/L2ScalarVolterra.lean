import NLS.ZakharovShabat.PhysicalL2Primitive

/-! # The scalar L2 Volterra pairing as a bounded bilinear map -/
noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Extending a curve by its endpoint values does not increase its uniform norm. -/
theorem norm_curveBoundedExtension_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (w : Curve E) : ‖curveBoundedExtension E w‖ ≤ ‖w‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg w)).mpr
  intro s
  exact w.norm_coe_le_norm _

/-- Integrating an L2 coefficient against a continuous test curve. -/
def l2ScalarVolterra (u : IntervalL2) : Curve ℂ →L[ℂ] Curve ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => intervalL2Primitive (curveBoundedExtension ℂ w) u
      map_add' := by
        intro w v
        ext t
        change (∫ s in (0 : ℝ)..t.val, u s*extend (w+v) s) =
          (∫ s in (0 : ℝ)..t.val, u s*extend w s)+(∫ s in (0 : ℝ)..t.val, u s*extend v s)
        simp only [NLS.LinearVolterra.extend,ContinuousMap.add_apply,mul_add]
        exact intervalIntegral.integral_add
          (intervalIntegrable_intervalL2_mul u (curveBoundedExtension ℂ w) t)
          (intervalIntegrable_intervalL2_mul u (curveBoundedExtension ℂ v) t)
      map_smul' := by
        intro c w
        ext t
        change (∫ s in (0 : ℝ)..t.val, u s*extend (c • w) s) =
          c • (∫ s in (0 : ℝ)..t.val, u s*extend w s)
        simp only [NLS.LinearVolterra.extend,ContinuousMap.smul_apply,smul_eq_mul]
        simp_rw [show ∀ s : ℝ, u s*(c*w (projIcc 0 1 (by norm_num) s)) =
          c*(u s*w (projIcc 0 1 (by norm_num) s)) by intro s; ring]
        exact intervalIntegral.integral_const_mul _ _ }
    ‖u‖ (by
      intro w
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro t
      exact (norm_intervalL2_integral_mul_le u (curveBoundedExtension ℂ w) t).trans
        (mul_le_mul_of_nonneg_left (norm_curveBoundedExtension_le w) (norm_nonneg u)))

@[simp] theorem l2ScalarVolterra_apply (u : IntervalL2) (w : Curve ℂ) (t : Icc (0 : ℝ) 1) :
    l2ScalarVolterra u w t = ∫ s in (0 : ℝ)..t.val, u s*extend w s := rfl

theorem norm_l2ScalarVolterra_le (u : IntervalL2) : ‖l2ScalarVolterra u‖ ≤ ‖u‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg u) _

/-- The coefficient-to-operator map is bounded complex linear in the original L2 norm. -/
def l2ScalarVolterraCLM : IntervalL2 →L[ℂ] (Curve ℂ →L[ℂ] Curve ℂ) :=
  LinearMap.mkContinuous
    { toFun := l2ScalarVolterra
      map_add' := by
        intro u v
        ext w t
        exact congrArg (fun g : Curve ℂ => g t)
          (map_add (intervalL2PrimitiveCLM (curveBoundedExtension ℂ w)) u v)
      map_smul' := by
        intro c u
        ext w t
        exact congrArg (fun g : Curve ℂ => g t)
          (map_smul (intervalL2PrimitiveCLM (curveBoundedExtension ℂ w)) c u) }
    1 (fun u => by simpa only [one_mul] using! norm_l2ScalarVolterra_le u)

@[simp] theorem l2ScalarVolterraCLM_apply (u : IntervalL2) :
    l2ScalarVolterraCLM u = l2ScalarVolterra u := rfl

end NLS.ZakharovShabat
