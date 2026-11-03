import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # A bounded cotangent identity from translation covariance

Differentiating the generator identity on a real form gives a bounded
extension of the derivative applied to the unbounded generator. The real
form spans the complex space, so the resulting operator identity holds
on every complex variation. No Hessian symmetry is required.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {H E F : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem fderiv_comp_eq_zero_of_real_zero
    (V : Submodule ℝ H)
    (hspan : ∀ h : H, ∃ x y : V, h = x.val+I • y.val)
    (J : H →L[ℂ] E) (f : E → F) (hf : DifferentiableAt ℂ f 0)
    (hz : ∀ b : V, f (J b.val) = 0) :
    (fderiv ℂ f 0).comp J = 0 := by
  have hf' : DifferentiableAt ℂ f (J (0 : H)) := by simpa only [map_zero] using hf
  have hd := ((hf'.hasFDerivAt.comp (0 : H) J.hasFDerivAt).restrictScalars ℝ).comp
    (0 : V) V.subtypeL.hasFDerivAt
  change HasFDerivAt (fun b : V => f (J b.val)) _ (0 : V) at hd
  have he : (fun b : V => f (J b.val)) = fun _ => 0 := funext hz
  rw [he] at hd
  have hconst : HasFDerivAt (fun _ : V => (0 : F)) (0 : V →L[ℝ] F) 0 := hasFDerivAt_const 0 0
  have hh := hd.unique hconst
  have hreal (x : V) : (fderiv ℂ f 0) (J x.val) = 0 := by
    have hv := congrArg (fun L : V →L[ℝ] F => L x) hh
    change (fderiv ℂ f (J (0 : H))) (J x.val) = 0 at hv
    simpa only [map_zero] using hv
  apply ContinuousLinearMap.ext
  intro h
  obtain ⟨x,y,rfl⟩ := hspan h
  simp only [ContinuousLinearMap.comp_apply,map_add,map_smul,hreal,smul_zero,add_zero,zero_apply]

theorem fderiv_generator_eq_of_real_covariance
    (V : Submodule ℝ H)
    (hspan : ∀ h : H, ∃ x y : V, h = x.val+I • y.val)
    (J D : H →L[ℂ] E) (R : F →L[ℂ] F) (f : E → F) (a : V)
    (hf : AnalyticAt ℂ f (J a.val))
    (hcov : ∀ b : V, (fderiv ℂ f (J b.val)) (D b.val) = R (f (J b.val))) :
    (fderiv ℂ f (J a.val)).comp D =
      (R.comp (fderiv ℂ f (J a.val))-
        (fderiv ℂ (fderiv ℂ f) (J a.val)).flip (D a.val)).comp J := by
  let A := fderiv ℂ f (J a.val)
  let B := fderiv ℂ (fderiv ℂ f) (J a.val)
  have hd := ((hf.fderiv.differentiableAt.hasFDerivAt.comp a.val J.hasFDerivAt).clm_apply D.hasFDerivAt).restrictScalars ℝ
  have hr := (R.hasFDerivAt.comp a.val (hf.differentiableAt.hasFDerivAt.comp a.val J.hasFDerivAt)).restrictScalars ℝ
  have hdV := hd.comp a V.subtypeL.hasFDerivAt
  have hrV := hr.comp a V.subtypeL.hasFDerivAt
  have he : (fun b : V => (fderiv ℂ f (J b.val)) (D b.val)) =
      (fun b : V => R (f (J b.val))) := funext hcov
  change HasFDerivAt (fun b : V => (fderiv ℂ f (J b.val)) (D b.val)) _ a at hdV
  change HasFDerivAt (fun b : V => R (f (J b.val))) _ a at hrV
  rw [he] at hdV
  have hreal (h : V) : A (D h.val) = R (A (J h.val))-B (J h.val) (D a.val) := by
    have hh := congrArg (fun L : V →L[ℝ] F => L h) (hdV.unique hrV)
    change A (D h.val)+B (J h.val) (D a.val) = R (A (J h.val)) at hh
    exact eq_sub_of_add_eq hh
  apply ContinuousLinearMap.ext
  intro h
  obtain ⟨x,y,rfl⟩ := hspan h
  simp only [ContinuousLinearMap.comp_apply,map_add,map_smul,sub_apply,
    ContinuousLinearMap.flip_apply]
  rw [hreal x,hreal y]

end NLS.ComplexAnalysis
