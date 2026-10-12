import NLS.ZakharovShabat.L2ScalarVolterra
import NLS.ZakharovShabat.L2VolterraEquation
import NLS.ZakharovShabat.ClassicalVolterraL2Bound
import NLS.FunctionalAnalysis.ForcedVolterraSolution

/-! # The actual L2 Volterra operator and its bounded parameter map -/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

private def firstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)
private def secondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)

private theorem norm_firstCurve_le (w : Curve (ℂ × ℂ)) : ‖firstCurve w‖ ≤ ‖w‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
  intro t
  exact (norm_fst_le (w t)).trans (w.norm_coe_le_norm t)
private theorem norm_secondCurve_le (w : Curve (ℂ × ℂ)) : ‖secondCurve w‖ ≤ ‖w‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg w)).mpr
  intro t
  exact (norm_snd_le (w t)).trans (w.norm_coe_le_norm t)

private theorem norm_scalarPrimitive_le (w : Curve ℂ) : ‖primitive w‖ ≤ ‖w‖ := by
  have h : ‖primitive (E := ℂ)‖ ≤ 1 := by
    apply (norm_volterra_le _).trans
    apply (ContinuousMap.norm_le _ (by norm_num)).mpr
    intro t
    exact ContinuousLinearMap.norm_id_le
  exact (primitive.le_opNorm w).trans (by simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right h (norm_nonneg w)))

/-- The original two signed component integrals as a continuous curve. -/
def l2VolterraCurve (q : ℂ × IntervalPairL2) (w : Curve (ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ((-I*q.1) • primitive (firstCurve w)+I • l2ScalarVolterraCLM q.2.fst (secondCurve w)).prodMk
    (-I • l2ScalarVolterraCLM q.2.snd (firstCurve w)+(I*q.1) • primitive (secondCurve w))

theorem l2VolterraCurve_apply (q : ℂ × IntervalPairL2) (w : Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) :
    l2VolterraCurve q w t = l2ODEIntegral q.2 q.1 w t := by
  rw [l2ODEIntegral_eq]
  simp only [l2VolterraCurve,ContinuousMap.prodMk,ContinuousMap.coe_mk,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,l2ScalarVolterraCLM_apply,l2ScalarVolterra_apply,primitive_apply,smul_eq_mul]
  rfl

/-- The original L2 norm controls the operator applied to any continuous curve. -/
theorem norm_l2VolterraCurve_le (q : ℂ × IntervalPairL2) (w : Curve (ℂ × ℂ)) :
    ‖l2VolterraCurve q w‖ ≤ (‖q.1‖+‖q.2‖)*‖w‖ := by
  have h₁ := (l2ScalarVolterra q.2.fst).le_opNorm (secondCurve w)
  have h₂ := (l2ScalarVolterra q.2.snd).le_opNorm (firstCurve w)
  have hb₁ : ‖l2ScalarVolterraCLM q.2.fst (secondCurve w)‖ ≤ ‖q.2‖*‖w‖ :=
    h₁.trans (mul_le_mul ((norm_l2ScalarVolterra_le _).trans (WithLp.norm_fst_le _ q.2))
      (norm_secondCurve_le w) (norm_nonneg _) (norm_nonneg _))
  have hb₂ : ‖l2ScalarVolterraCLM q.2.snd (firstCurve w)‖ ≤ ‖q.2‖*‖w‖ :=
    h₂.trans (mul_le_mul ((norm_l2ScalarVolterra_le _).trans (WithLp.norm_snd_le _ q.2))
      (norm_firstCurve_le w) (norm_nonneg _) (norm_nonneg _))
  have hp₁ := (norm_scalarPrimitive_le (firstCurve w)).trans (norm_firstCurve_le w)
  have hp₂ := (norm_scalarPrimitive_le (secondCurve w)).trans (norm_secondCurve_le w)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change max ‖((-I*q.1) • primitive (firstCurve w)+I • l2ScalarVolterraCLM q.2.fst (secondCurve w)) t‖
    ‖(-I • l2ScalarVolterraCLM q.2.snd (firstCurve w)+(I*q.1) • primitive (secondCurve w)) t‖ ≤ _
  apply max_le
  · apply (ContinuousMap.norm_coe_le_norm _ t).trans
    apply (norm_add_le _ _).trans
    simp only [norm_smul,norm_mul,norm_neg,norm_I,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hp₁ (norm_nonneg q.1)]
  · apply (ContinuousMap.norm_coe_le_norm _ t).trans
    apply (norm_add_le _ _).trans
    simp only [norm_smul,norm_mul,norm_neg,norm_I,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hp₂ (norm_nonneg q.1)]

/-- The actual integral operator, linear in its test curve. -/
def l2Volterra (q : ℂ × IntervalPairL2) : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  LinearMap.mkContinuous
    { toFun := l2VolterraCurve q
      map_add' := by
        intro w v
        ext t <;> simp [l2VolterraCurve,ContinuousMap.prodMk,map_add,smul_eq_mul] <;> ring
      map_smul' := by
        intro c w
        ext t <;> simp [l2VolterraCurve,ContinuousMap.prodMk,map_smul,smul_eq_mul] <;> ring }
    (‖q.1‖+‖q.2‖) (norm_l2VolterraCurve_le q)

@[simp] theorem l2Volterra_apply (q : ℂ × IntervalPairL2) (w : Curve (ℂ × ℂ)) (t : Icc (0 : ℝ) 1) :
    l2Volterra q w t = l2ODEIntegral q.2 q.1 w t := l2VolterraCurve_apply q w t

theorem norm_l2Volterra_le (q : ℂ × IntervalPairL2) : ‖l2Volterra q‖ ≤ ‖q.1‖+‖q.2‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Frequency and physical L2 potential enter the operator through a bounded complex-linear map. -/
def l2VolterraCoefficientMap : (ℂ × IntervalPairL2) →L[ℂ] (Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ)) :=
  LinearMap.mkContinuous
    { toFun := l2Volterra
      map_add' := by
        intro q r
        apply ContinuousLinearMap.ext
        intro w
        change l2VolterraCurve (q+r) w = l2VolterraCurve q w+l2VolterraCurve r w
        ext t <;> simp [l2VolterraCurve,map_add,smul_eq_mul] <;> ring
      map_smul' := by
        intro c q
        apply ContinuousLinearMap.ext
        intro w
        change l2VolterraCurve (c • q) w = c • l2VolterraCurve q w
        ext t <;> simp [l2VolterraCurve,ContinuousMap.prodMk,map_smul,smul_eq_mul] <;> ring }
    2 (fun q => by
      change ‖l2Volterra q‖ ≤ _
      exact (norm_l2Volterra_le q).trans (by nlinarith [norm_fst_le q,norm_snd_le q]))

@[simp] theorem l2VolterraCoefficientMap_apply (q : ℂ × IntervalPairL2) :
    l2VolterraCoefficientMap q = l2Volterra q := rfl

/-- The operator agrees exactly with the original continuous-coefficient Volterra map. -/
theorem l2Volterra_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2Volterra (z,continuousPotentialL2Class φ) = volterra (classicalCoefficientCurveCLM (z,φ)) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousMap.ext
  intro t
  rw [l2Volterra_apply,l2ODEIntegral_of_continuous,volterra_apply]
  rfl

/-- Changing only the potential is Lipschitz in the original L2 norm. -/
theorem norm_l2Volterra_sub_le (u v : IntervalPairL2) (z : ℂ) :
    ‖l2Volterra (z,u)-l2Volterra (z,v)‖ ≤ ‖u-v‖ := by
  change ‖l2VolterraCoefficientMap (z,u)-l2VolterraCoefficientMap (z,v)‖ ≤ _
  rw [← map_sub l2VolterraCoefficientMap (z,u) (z,v)]
  simpa using norm_l2Volterra_le ((z,u)-(z,v))

end NLS.ZakharovShabat
