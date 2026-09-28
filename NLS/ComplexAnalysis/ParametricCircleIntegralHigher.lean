import NLS.ComplexAnalysis.ParametricCircleIntegral
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# Higher source regularity of a parametric contour integral

The parameter derivative of a jointly analytic integrand is itself
jointly analytic with values in the Banach space of continuous linear
maps. This lets the Banach-valued differentiation-under-the-integral
theorem be applied again to the first derivative.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ContDiff
namespace NLS.ComplexAnalysis

universe u
variable {A B : Type u} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

/-- The joint derivative of an analytic integrand, restricted to
parameter directions, is an analytic operator-valued function. -/
theorem analyticOnNhd_parameterDerivative
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hF : AnalyticOnNhd ℂ F D) :
    AnalyticOnNhd ℂ
      (fun t : ℂ × A =>
        (fderiv ℂ F t).comp (ContinuousLinearMap.inr ℂ ℂ A)) D := by
  let C : (ℂ × A →L[ℂ] B) →L[ℂ] (A →L[ℂ] B) :=
    (ContinuousLinearMap.compL ℂ A (ℂ × A) B).flip
      (ContinuousLinearMap.inr ℂ ℂ A)
  change AnalyticOnNhd ℂ (fun t => C (fderiv ℂ F t)) D
  exact C.comp_analyticOnNhd hF.fderiv

/-- On an open parameter domain whose fixed circle stays inside the
joint analytic domain, the derivative of the circle integral is the
circle integral of the parameter-direction derivative. -/
theorem hasFDerivAt_circleIntegral_parameterDerivative
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    {V : Set A} (_hVopen : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c R, (z,a) ∈ D)
    (a : A) (ha : a ∈ V) :
    HasFDerivAt (fun b : A => ∮ z in C(c,R), F (z,b))
      (∮ z in C(c,R),
        (fderiv ℂ F (z,a)).comp (ContinuousLinearMap.inr ℂ ℂ A)) a := by
  obtain ⟨W,hWopen,haW,M,_,hbound⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hF c R a (hcircle a ha)
  have hdom (b : A) (hb : b ∈ W) (θ : ℝ) :
      (circleMap c R θ,b) ∈ D :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).1
  have hderBound (b : A) (hb : b ∈ W) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M :=
    (hbound _ (circleMap_mem_sphere c hR θ) b hb).2
  simpa only [circleIntegral] using
    hasFDerivAt_circleIntegral_of_jointAnalytic
      F D hDopen hF c R hR W hWopen a haW M hdom hderBound

/-- Every finite complex differentiability order of a fixed-circle
integral follows by iterating the Banach-valued parameter derivative
formula. -/
theorem contDiffOn_nat_circleIntegral_of_jointAnalytic
    (k : ℕ) (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    {V : Set A} (hVopen : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c R, (z,a) ∈ D) :
    ContDiffOn ℂ k (fun a : A => ∮ z in C(c,R), F (z,a)) V := by
  induction k generalizing B F D V hDopen hF hVopen hcircle with
  | zero =>
      apply contDiffOn_zero.mpr
      intro a ha
      exact (hasFDerivAt_circleIntegral_parameterDerivative
        F hDopen hF c R hR hVopen hcircle a ha).continuousAt.continuousWithinAt
  | succ k ih =>
      let I : A → B := fun a => ∮ z in C(c,R), F (z,a)
      let G : ℂ × A → (A →L[ℂ] B) := fun t =>
        (fderiv ℂ F t).comp (ContinuousLinearMap.inr ℂ ℂ A)
      let J : A → (A →L[ℂ] B) := fun a => ∮ z in C(c,R), G (z,a)
      have hG : AnalyticOnNhd ℂ G D :=
        analyticOnNhd_parameterDerivative F hF
      have hIat (a : A) (ha : a ∈ V) : HasFDerivAt I (J a) a := by
        exact hasFDerivAt_circleIntegral_parameterDerivative
          F hDopen hF c R hR hVopen hcircle a ha
      have hIdiff : DifferentiableOn ℂ I V :=
        fun a ha => (hIat a ha).differentiableAt.differentiableWithinAt
      have hJ : ContDiffOn ℂ k J V :=
        ih G hDopen hG hVopen hcircle
      have hDeriv : ContDiffOn ℂ k (fderiv ℂ I) V :=
        hJ.congr (fun a ha => (hIat a ha).fderiv)
      have hsucc : ContDiffOn ℂ ((k : ℕ∞ω) + 1) I V :=
        (contDiffOn_succ_iff_fderiv_of_isOpen hVopen).2
          ⟨hIdiff,by simp,hDeriv⟩
      simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsucc

/-- A jointly analytic integrand has a complex-smooth fixed-circle
integral on every open parameter domain whose circles stay in the
joint domain. -/
theorem contDiffOn_infty_circleIntegral_of_jointAnalytic
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    {V : Set A} (hVopen : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c R, (z,a) ∈ D) :
    ContDiffOn ℂ ∞ (fun a : A => ∮ z in C(c,R), F (z,a)) V :=
  contDiffOn_infty.mpr (fun k =>
    contDiffOn_nat_circleIntegral_of_jointAnalytic
      k F hDopen hF c R hR hVopen hcircle)

/-- Joint analyticity of an integrand passes through integration on
a fixed circle when that circle stays inside the joint domain on an
open parameter set. This yields an actual Banach power series in the
parameter, not only Fréchet differentiability. -/
theorem analyticOnNhd_circleIntegral_of_jointAnalytic
    (F : ℂ × A → B) {D : Set (ℂ × A)}
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    {V : Set A} (hVopen : IsOpen V)
    (hcircle : ∀ a ∈ V, ∀ z ∈ sphere c R, (z,a) ∈ D) :
    AnalyticOnNhd ℂ
      (fun a : A => ∮ z in C(c,R), F (z,a)) V :=
  analyticOnNhd_of_complexSmoothOn _ hVopen
    (contDiffOn_infty_circleIntegral_of_jointAnalytic
      F hDopen hF c R hR hVopen hcircle)

end NLS.ComplexAnalysis
