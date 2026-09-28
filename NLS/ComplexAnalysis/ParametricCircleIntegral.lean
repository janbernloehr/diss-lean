import NLS.ComplexAnalysis.UniformJointDerivativeCircle
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Differentiating a fixed circle integral in a Banach parameter

Joint analyticity gives a source derivative along each point of a
fixed circle. A uniform derivative bound on the circle permits
differentiation under its angle integral.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory
open scoped Interval
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

/-- The Fréchet derivative of a fixed-circle integral is the angle
integral of the parameter derivative of its jointly analytic
integrand. -/
theorem hasFDerivAt_circleIntegral_of_jointAnalytic
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hVopen : IsOpen V) (a : A) (haV : a ∈ V)
    (M : ℝ)
    (hdom : ∀ b ∈ V, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D)
    (hbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M) :
    HasFDerivAt (fun b : A => ∮ z in C(c, R), F (z,b))
      (∫ θ in (0:ℝ)..2*Real.pi,
        (deriv (circleMap c R) θ) •
          (fderiv ℂ F (circleMap c R θ,a)).comp
            (ContinuousLinearMap.inr ℂ ℂ A)) a := by
  let J : A →L[ℂ] ℂ × A := ContinuousLinearMap.inr ℂ ℂ A
  let G : A → ℝ → B := fun b θ =>
    deriv (circleMap c R) θ • F (circleMap c R θ,b)
  let G' : A → ℝ → A →L[ℂ] B := fun b θ =>
    (deriv (circleMap c R) θ) •
      (fderiv ℂ F (circleMap c R θ,b)).comp J
  have hmap (b : A) : Continuous (fun θ : ℝ => (circleMap c R θ,b)) :=
    (continuous_circleMap c R).prodMk continuous_const
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hGcont (b : A) (hb : b ∈ V) : Continuous (G b) := by
    have hsection : Continuous (fun θ : ℝ => F (circleMap c R θ,b)) :=
      hF.continuousOn.comp_continuous (hmap b) (hdom b hb)
    exact hderiv.smul hsection
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hDopen (by norm_num)
  have hG'cont (b : A) (hb : b ∈ V) : Continuous (G' b) := by
    have hsection : Continuous (fun θ : ℝ => fderiv ℂ F (circleMap c R θ,b)) :=
      hdf.comp_continuous (hmap b) (hdom b hb)
    exact hderiv.smul (hsection.clm_comp continuous_const)
  have hmeas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (G b) (volume.restrict (Ι (0:ℝ) (2*Real.pi))) :=
    by
      filter_upwards [hVopen.mem_nhds haV] with b hb
      exact (hGcont b hb).aestronglyMeasurable
  have hint : IntervalIntegrable (G a) volume 0 (2*Real.pi) :=
    (hGcont a haV).intervalIntegrable _ _
  have hmeas' : AEStronglyMeasurable (G' a)
      (volume.restrict (Ι (0:ℝ) (2*Real.pi))) :=
    (hG'cont a haV).aestronglyMeasurable
  have hderiv_bound (b : A) (hb : b ∈ V) (θ : ℝ) :
      ‖G' b θ‖ ≤ R*M := by
    have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℂ ℂ A
    have hnorm : ‖deriv (circleMap c R) θ‖ = R := by
      simp [deriv_circleMap, abs_of_nonneg hR]
    calc
      ‖G' b θ‖ = R * ‖(fderiv ℂ F (circleMap c R θ,b)).comp J‖ := by
        simp only [G', norm_smul, hnorm]
      _ ≤ R * ‖fderiv ℂ F (circleMap c R θ,b)‖ := by
        apply mul_le_mul_of_nonneg_left _ hR
        calc
          ‖(fderiv ℂ F (circleMap c R θ,b)).comp J‖ ≤
              ‖fderiv ℂ F (circleMap c R θ,b)‖ * ‖J‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ ‖fderiv ℂ F (circleMap c R θ,b)‖ := by
            nlinarith [norm_nonneg (fderiv ℂ F (circleMap c R θ,b))]
      _ ≤ R*M := mul_le_mul_of_nonneg_left (hbound b hb θ) hR
  have hdiff (θ : ℝ) (b : A) (hb : b ∈ V) :
      HasFDerivAt (fun x : A => G x θ) (G' b θ) b := by
    have hinc : HasFDerivAt (fun x : A => (circleMap c R θ,x)) J b :=
      hasFDerivAt_prodMk_right (circleMap c R θ) b
    have hcomp := ((hF _ (hdom b hb θ)).differentiableAt.hasFDerivAt.comp b hinc)
    have hfun :
        (deriv (circleMap c R) θ • fun x : A => F (circleMap c R θ,x)) =
          (fun x : A => deriv (circleMap c R) θ • F (circleMap c R θ,x)) := by
      funext x
      rfl
    simpa only [G, G', Function.comp_def, hfun] using
      hcomp.const_smul (deriv (circleMap c R) θ)
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := G) (F' := G') (s := V) (x₀ := a) (bound := fun _ : ℝ => R*M)
    (hVopen.mem_nhds haV) hmeas hint hmeas'
    (Filter.Eventually.of_forall fun θ _ b hb => hderiv_bound b hb θ)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ b hb => hdiff θ b hb)
  change HasFDerivAt (fun b : A => ∫ θ in (0:ℝ)..2*Real.pi, G b θ)
    (∫ θ in (0:ℝ)..2*Real.pi, G' a θ) a
  exact hmain

/-- Evaluate the source Fréchet derivative of a jointly analytic
circle integral in a direction as the circle integral of the source
derivative of its integrand. -/
theorem fderiv_circleIntegral_apply_of_jointAnalytic
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hVopen : IsOpen V) (a : A) (haV : a ∈ V)
    (M : ℝ)
    (hdom : ∀ b ∈ V, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D)
    (hbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M)
    (h : A) :
    (fderiv ℂ (fun b : A => ∮ z in C(c,R), F (z,b)) a) h =
      ∮ z in C(c,R), (fderiv ℂ (fun b : A => F (z,b)) a) h := by
  have hmain := (hasFDerivAt_circleIntegral_of_jointAnalytic
    F D hDopen hF c R hR V hVopen a haV M hdom hbound).fderiv
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hDopen (by norm_num)
  have hmap : Continuous (fun θ : ℝ => (circleMap c R θ,a)) :=
    (continuous_circleMap c R).prodMk continuous_const
  have hsection : Continuous (fun θ : ℝ => fderiv ℂ F (circleMap c R θ,a)) :=
    hdf.comp_continuous hmap (hdom a haV)
  have hderiv : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  have hθ : Continuous (fun θ : ℝ =>
      (deriv (circleMap c R) θ) •
        (fderiv ℂ F (circleMap c R θ,a)).comp
          (ContinuousLinearMap.inr ℂ ℂ A)) :=
    hderiv.smul (hsection.clm_comp continuous_const)
  have hint : IntervalIntegrable (fun θ : ℝ =>
      (deriv (circleMap c R) θ) •
        (fderiv ℂ F (circleMap c R θ,a)).comp
          (ContinuousLinearMap.inr ℂ ℂ A)) volume 0 (2*Real.pi) :=
    hθ.intervalIntegrable _ _
  calc
    (fderiv ℂ (fun b : A => ∮ z in C(c,R), F (z,b)) a) h =
        (∫ θ in (0:ℝ)..2*Real.pi,
          (deriv (circleMap c R) θ) •
            (fderiv ℂ F (circleMap c R θ,a)).comp
              (ContinuousLinearMap.inr ℂ ℂ A)) h := congrArg (· h) hmain
    _ = ∫ θ in (0:ℝ)..2*Real.pi,
          ((deriv (circleMap c R) θ) •
            (fderiv ℂ F (circleMap c R θ,a)).comp
              (ContinuousLinearMap.inr ℂ ℂ A)) h :=
      ContinuousLinearMap.intervalIntegral_apply hint h
    _ = ∮ z in C(c,R),
          (fderiv ℂ (fun b : A => F (z,b)) a) h := by
      unfold circleIntegral
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [fderiv_source_section_eq_joint F (circleMap c R θ) a
        ((hF _ (hdom a haV θ)).differentiableAt)]
      simp

/-- A jointly analytic integrand with a uniform joint derivative bound
on a fixed circle has a complex Fréchet-differentiable circle integral
in its Banach-space parameter. -/
theorem differentiableAt_circleIntegral_of_jointAnalytic
    (F : ℂ × A → B) (D : Set (ℂ × A))
    (hDopen : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hVopen : IsOpen V) (a : A) (haV : a ∈ V)
    (M : ℝ)
    (hdom : ∀ b ∈ V, ∀ θ : ℝ, (circleMap c R θ,b) ∈ D)
    (hbound : ∀ b ∈ V, ∀ θ : ℝ,
      ‖fderiv ℂ F (circleMap c R θ,b)‖ ≤ M) :
    DifferentiableAt ℂ (fun b : A => ∮ z in C(c, R), F (z,b)) a :=
  (hasFDerivAt_circleIntegral_of_jointAnalytic F D hDopen hF
    c R hR V hVopen a haV M hdom hbound).differentiableAt

end NLS.ComplexAnalysis
