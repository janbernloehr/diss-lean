import NLS.ComplexAnalysis.QuadraticSheetTerminalVariation
import NLS.ComplexAnalysis.MovingSpectralParameter
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Full source differentiation of an actual moving quadratic-sheet
terminal. Symmetric data and the interior primitive are stationary;
the moving multiplier derivative cancels using the actual sheet-square
identity. The terminal sheet itself is allowed to vanish. -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fderiv_moving_quadratic_sheet_terminal_cleared
    (H : ℂ × E → ℂ) (μ M G δ K B : E → ℂ) (a h : E) (g : ℂ)
    (hH : DifferentiableAt ℂ H (μ a,a))
    (hμ : DifferentiableAt ℂ μ a) (hM : DifferentiableAt ℂ M a)
    (hG : DifferentiableAt ℂ G a) (hδ : DifferentiableAt ℂ δ a)
    (hK : DifferentiableAt ℂ K a) (hne : K a ≠ 0)
    (hMG : (fderiv ℂ M a) h = 0 ∧ (fderiv ℂ G a) h = 0)
    (hHzero : (fderiv ℂ (fun b => H (μ a,b)) a) h = 0)
    (hsq : (fun b => δ b^2) =ᶠ[𝓝 a]
      (fun b => K b^2*((μ b-M b)^2-G b/4)))
    (hB : B =ᶠ[𝓝 a] (fun b => δ b/K b*H (μ b,b)))
    (heq : ((μ a-M a)^2-G a/4)*deriv (fun z => H (z,a)) (μ a)+
      (μ a-M a)*H (μ a,a) = g) :
    δ a*((fderiv ℂ B a) h) = K a*g*((fderiv ℂ μ a) h) := by
  let Q : E → ℂ := fun b => (μ b-M b)^2-G b/4
  let F : E → ℂ := fun b => H (μ b,b)
  have hF : DifferentiableAt ℂ F a :=
    hH.comp a (f := fun b : E => (μ b,b)) (hμ.prodMk differentiableAt_id)
  have hFzero : (fderiv ℂ F a) h =
      deriv (fun z => H (z,a)) (μ a)*((fderiv ℂ μ a) h) := by
    rw [fderiv_moving_spectral_parameter H μ a hH hμ]
    simp only [add_apply,smul_apply,smul_eq_mul,hHzero,zero_add]
  have hQ := ((hμ.hasFDerivAt.fun_sub hM.hasFDerivAt).pow 2).fun_sub
    (hG.hasFDerivAt.mul_const (4:ℂ)⁻¹)
  change HasFDerivAt Q _ a at hQ
  have hQeval : (fderiv ℂ Q a) h = 2*(μ a-M a)*((fderiv ℂ μ a) h) := by
    rw [hQ.fderiv]
    simp only [sub_apply,smul_apply,smul_eq_mul,hMG.1,hMG.2,sub_zero,mul_zero]
    ring
  have hleft := hδ.hasFDerivAt.pow 2
  have hright := (hK.hasFDerivAt.pow 2).fun_mul hQ
  change HasFDerivAt (fun b => δ b^2) _ a at hleft
  change HasFDerivAt (fun b => K b^2*Q b) _ a at hright
  have hsheet : δ a*((fderiv ℂ δ a) h) =
      K a*((fderiv ℂ K a) h)*Q a+K a^2*(μ a-M a)*((fderiv ℂ μ a) h) := by
    have hv := congrArg (fun L : E →L[ℂ] ℂ => L h) hsq.fderiv_eq
    change (fderiv ℂ (fun b => δ b^2) a) h =
      (fderiv ℂ (fun b => K b^2*Q b) a) h at hv
    rw [hleft.fderiv,hright.fderiv] at hv
    simp only [add_apply,smul_apply,smul_eq_mul] at hv
    have hQe := congrArg (fun L : E →L[ℂ] ℂ => L h) hQ.fderiv
    rw [← hQe,hQeval] at hv
    linear_combination hv/2
  have hi := (hasFDerivAt_inv hne).comp a hK.hasFDerivAt
  have hdB := (hδ.hasFDerivAt.fun_mul hi).fun_mul hF.hasFDerivAt
  simp only [Function.comp_def] at hdB
  have hBclear : K a^2*((fderiv ℂ B a) h) =
      (((fderiv ℂ δ a) h)*K a-δ a*((fderiv ℂ K a) h))*H (μ a,a)+
        δ a*K a*deriv (fun z => H (z,a)) (μ a)*((fderiv ℂ μ a) h) := by
    have hnear : B =ᶠ[𝓝 a] (fun b => δ b*(K b)⁻¹*F b) := by
      simpa only [div_eq_mul_inv,F] using hB
    rw [hnear.fderiv_eq,hdB.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    rw [hFzero]
    field_simp [hne]
    ring
  exact quadratic_sheet_terminal_variation (δ a) (K a) (Q a) (μ a-M a)
    (H (μ a,a)) (deriv (fun z => H (z,a)) (μ a)) g ((fderiv ℂ μ a) h)
    ((fderiv ℂ δ a) h) ((fderiv ℂ K a) h) ((fderiv ℂ B a) h) hne
    hsq.eq_of_nhds hsheet heq hBclear

end NLS.ComplexAnalysis
