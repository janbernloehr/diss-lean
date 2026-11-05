import NLS.ComplexAnalysis.CircleSourceStationarity
import NLS.ComplexAnalysis.ParametricCircleTransforms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem parametricCircleCauchyTransform_source_fderiv_eq_zero
    (F : ℂ × A → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (p h : A)
    (hF : ∀ w∈sphere c r, AnalyticAt ℂ F (w,p))
    (hzero : ∀ w∈sphere c r, (fderiv ℂ (fun b : A => F (w,b)) p) h=0)
    (z : ℂ) (hz : z∉sphere c r) :
    DifferentiableAt ℂ (fun b : A => parametricCircleCauchyTransform F c r (z,b)) p ∧
      (fderiv ℂ (fun b : A => parametricCircleCauchyTransform F c r (z,b)) p) h=0 := by
  let D : Set (ℂ × A) := {t | AnalyticAt ℂ F t ∧ t.1≠z}
  have hD : IsOpen D := (isOpen_analyticAt ℂ F).inter (isOpen_ne_fun continuous_fst continuous_const)
  let G : ℂ × A → ℂ := fun t => F t/(t.1-z)
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    exact ht.1.div (analyticAt_fst.sub analyticAt_const) (sub_ne_zero.mpr ht.2)
  have hne (w : ℂ) (hw : w∈sphere c r) : w≠z := fun he => hz (he ▸ hw)
  have hker (w : ℂ) (hw : w∈sphere c r) : (fderiv ℂ (fun b : A => G (w,b)) p) h=0 := by
    have hs : AnalyticAt ℂ (fun b : A => F (w,b)) p :=
      (hF w hw).comp (f := fun b : A => (w,b)) (analyticAt_const.prod analyticAt_id)
    change (fderiv ℂ (fun b : A => F (w,b)/(w-z)) p) h=0
    have hd := hs.differentiableAt.hasFDerivAt.mul_const (w-z)⁻¹
    change HasFDerivAt (fun b : A => F (w,b)/(w-z)) _ p at hd
    rw [hd.fderiv]
    simp only [smul_apply,smul_eq_mul,hzero w hw,mul_zero]
  have hc := circleIntegral_source_fderiv_eq_zero G D hD hG c r hr p h
    (fun w hw => ⟨hF w hw,hne w hw⟩) hker
  refine ⟨hc.1.const_mul (2*Real.pi*I)⁻¹,?_⟩
  change (fderiv ℂ (fun b : A => (2*Real.pi*I)⁻¹*(∮ w in C(c,r),G (w,b))) p) h=0
  rw [fderiv_const_mul hc.1]
  simp only [smul_apply,smul_eq_mul,hc.2,mul_zero]

end NLS.ComplexAnalysis
