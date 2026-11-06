import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.JointSpectralDerivative

/-! # Joint analytic divided differences with a moving center

A fixed real-interval integral of the spectral derivative fills the
apparent pole. It is analytic simultaneously in the spectral point and
Banach parameter, including on the moving diagonal.
-/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Entire-slice divided difference at zero, filled by its derivative. -/
def parametricZeroDividedDifference (F : ℂ × A → ℂ) (x : ℂ × A) : ℂ :=
  ∫ t in (0 : ℝ)..1, deriv (fun z => F (z,x.2)) ((t : ℂ)*x.1)

theorem analyticOnNhd_parametricZeroDividedDifference
    (F : ℂ × A → ℂ) {V : Set A} (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricZeroDividedDifference F) (univ ×ˢ V) := by
  let D := fun x : ℂ × A => deriv (fun z => F (z,x.2)) x.1
  have hD : AnalyticOnNhd ℂ D (univ ×ˢ V) :=
    analyticOnNhd_spectral_deriv_of_analyticOnNhd F _ (isOpen_univ.prod hV) hF
  let G := fun x : ℂ × (ℂ × A) => D (x.1*x.2.1,x.2.2)
  have hG : AnalyticOnNhd ℂ G (univ ×ˢ (univ ×ˢ V)) := by
    intro x hx
    have hz : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.1) x :=
      analyticAt_fst.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    have ha : AnalyticAt ℂ (fun x : ℂ × (ℂ × A) => x.2.2) x :=
      analyticAt_snd.comp (f := fun x : ℂ × (ℂ × A) => x.2) analyticAt_snd
    exact (hD (x.1*x.2.1,x.2.2) ⟨mem_univ _,hx.2.2⟩).comp
      (f := fun x : ℂ × (ℂ × A) => (x.1*x.2.1,x.2.2)) ((analyticAt_fst.mul hz).prod ha)
  exact analyticOnNhd_intervalIntegral_of_jointAnalytic G
    (isOpen_univ.prod (isOpen_univ.prod hV)) hG 0 1 (isOpen_univ.prod hV)
    (fun x hx _ _ => ⟨mem_univ _,hx⟩)

theorem parametricZeroDividedDifference_mul
    (F : ℂ × A → ℂ) {V : Set A} (hF : AnalyticOnNhd ℂ F (univ ×ˢ V))
    (z : ℂ) (a : A) (ha : a ∈ V) :
    z*parametricZeroDividedDifference F (z,a) = F (z,a)-F (0,a) := by
  let D := fun x : ℂ × A => deriv (fun w => F (w,x.2)) x.1
  have hFa : AnalyticOnNhd ℂ (fun w => F (w,a)) univ := by
    intro w _
    exact (hF (w,a) ⟨mem_univ _,ha⟩).comp (f := fun w : ℂ => (w,a))
      (analyticAt_id.prod analyticAt_const)
  have hDa : ContinuousOn (fun w => D (w,a)) univ := by
    intro w hw
    exact ((hFa w hw).deriv).continuousAt.continuousWithinAt
  have h := parametricConvexPrimitive_eq_sub_of_primitive D univ 0 a convex_univ
    (mem_univ _) hDa (fun w => F (w,a))
    (fun w hw => (hFa w hw).differentiableAt.hasDerivAt) z (mem_univ _)
  simpa only [parametricConvexPrimitive, sub_zero, zero_add, D,
    intervalIntegral.integral_const_mul, parametricZeroDividedDifference] using h

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
@[simp] theorem parametricZeroDividedDifference_zero (F : ℂ × A → ℂ) (a : A) :
    parametricZeroDividedDifference F (0,a) = deriv (fun z => F (z,a)) 0 := by
  simp [parametricZeroDividedDifference]

/-- The actual divided difference at an arbitrary moving spectral center. -/
def parametricMovingDividedDifference (F : ℂ × A → ℂ) (μ : A → ℂ) (x : ℂ × A) : ℂ :=
  parametricZeroDividedDifference (fun t : ℂ × A => F (μ t.2+t.1,t.2)) (x.1-μ x.2,x.2)

theorem analyticOnNhd_parametricMovingDividedDifference
    (F : ℂ × A → ℂ) (μ : A → ℂ) {V : Set A} (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (hμ : AnalyticOnNhd ℂ μ V) :
    AnalyticOnNhd ℂ (parametricMovingDividedDifference F μ) (univ ×ˢ V) := by
  have hshift : AnalyticOnNhd ℂ (fun t : ℂ × A => F (μ t.2+t.1,t.2)) (univ ×ˢ V) := by
    intro t ht
    have hm := (hμ t.2 ht.2).comp (f := fun t : ℂ × A => t.2) analyticAt_snd
    exact (hF (μ t.2+t.1,t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun t : ℂ × A => (μ t.2+t.1,t.2)) ((hm.add analyticAt_fst).prod analyticAt_snd)
  have hzero := analyticOnNhd_parametricZeroDividedDifference _ hV hshift
  intro t ht
  have hm := (hμ t.2 ht.2).comp (f := fun t : ℂ × A => t.2) analyticAt_snd
  exact (hzero (t.1-μ t.2,t.2) ⟨mem_univ _,ht.2⟩).comp
    (f := fun t : ℂ × A => (t.1-μ t.2,t.2)) ((analyticAt_fst.sub hm).prod analyticAt_snd)

theorem parametricMovingDividedDifference_mul
    (F : ℂ × A → ℂ) (μ : A → ℂ) {V : Set A}
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (hμ : AnalyticOnNhd ℂ μ V)
    (z : ℂ) (a : A) (ha : a ∈ V) :
    (z-μ a)*parametricMovingDividedDifference F μ (z,a) = F (z,a)-F (μ a,a) := by
  have hshift : AnalyticOnNhd ℂ (fun t : ℂ × A => F (μ t.2+t.1,t.2)) (univ ×ˢ V) := by
    intro t ht
    have hm := (hμ t.2 ht.2).comp (f := fun t : ℂ × A => t.2) analyticAt_snd
    exact (hF (μ t.2+t.1,t.2) ⟨mem_univ _,ht.2⟩).comp
      (f := fun t : ℂ × A => (μ t.2+t.1,t.2)) ((hm.add analyticAt_fst).prod analyticAt_snd)
  simpa only [parametricMovingDividedDifference, add_sub_cancel, add_zero] using
    parametricZeroDividedDifference_mul _ hshift (z-μ a) a ha

theorem parametricMovingDividedDifference_center
    (F : ℂ × A → ℂ) (μ : A → ℂ) {V : Set A}
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (a : A) (ha : a ∈ V) :
    parametricMovingDividedDifference F μ (μ a,a) = deriv (fun z => F (z,a)) (μ a) := by
  simp only [parametricMovingDividedDifference, sub_self, parametricZeroDividedDifference_zero]
  have hd := ((hF (μ a,a) ⟨mem_univ _,ha⟩).comp
    (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
  have hd' : HasDerivAt (fun z : ℂ => F (z,a))
      (deriv (fun z => F (z,a)) (μ a)) (μ a+0) := by simpa only [Function.comp_def, add_zero] using! hd
  have hc : HasDerivAt (fun w : ℂ => μ a+w) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add (μ a)
  have h := hd'.comp (h := fun w : ℂ => μ a+w) 0 hc
  simpa only [Function.comp_def, mul_one] using! h.deriv

theorem parametricMovingDividedDifference_eq_dslope
    (F : ℂ × A → ℂ) (μ : A → ℂ) {V : Set A}
    (hF : AnalyticOnNhd ℂ F (univ ×ˢ V)) (hμ : AnalyticOnNhd ℂ μ V)
    (z : ℂ) (a : A) (ha : a ∈ V) :
    parametricMovingDividedDifference F μ (z,a) = dslope (fun w => F (w,a)) (μ a) z := by
  by_cases hz : z = μ a
  · subst z
    rw [parametricMovingDividedDifference_center F μ hF a ha, dslope_same]
  · rw [dslope_of_ne _ hz, slope_def_field]
    apply (eq_div_iff (sub_ne_zero.mpr hz)).mpr
    simpa only [mul_comm] using parametricMovingDividedDifference_mul F μ hF hμ z a ha

end NLS.ComplexAnalysis
