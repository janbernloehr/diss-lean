import NLS.ZakharovShabat.ClassicalScalarForcingFreeComparison
import NLS.ZakharovShabat.NLSWKBComparison

/-! # The exact diagonal forced-response identity

Integration by parts in the actual forced system isolates the upper diagonal response, including at zero spectral parameter.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Integration by parts in the actual scalar forced system isolates the
upper response's diagonal phase term. The identity is valid even at z=0. -/
theorem classicalScalarForcing_fst_integral_identity
    (a b f : ℝ → ℂ) (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : Continuous f)
    (z : ℂ) (t : Icc (0:ℝ) 1) :
    let Φ := classicalPotentialOfFunctions a b ha.continuous hb
    let Y := classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z
    (2*I*z)*(Y t).1 = I*a t*(Y t).2-
      exp (-I*z*t.val)*(∫ x in (0:ℝ)..t.val, exp (I*z*x)*
        (I*deriv a x*(Y x).2+a x*b x*(Y x).1+I*a x*f x)) := by
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb
  let Y := classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z
  let P (x : ℝ) := exp (I*z*x)*((2*I*z)*(Y x).1-I*a x*(Y x).2)
  let F (x : ℝ) := exp (I*z*x)*(I*deriv a x*(Y x).2+a x*b x*(Y x).1+I*a x*f x)
  have hY : Continuous Y := continuous_classicalForcedKernelSolution _ _ _
  have hda : Continuous (deriv a) := ha.continuous_deriv (by norm_num)
  have hP : Continuous P := by dsimp only [P]; fun_prop
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hd (x : Icc (0:ℝ) 1) : HasDerivAt P (-F x) x := by
    have hy := hasDerivAt_classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z x
    have h₁ := HasFDerivAt.hasDerivAt hy.fst
    have h₂ := HasFDerivAt.hasDerivAt hy.snd
    have he : HasDerivAt (fun y : ℝ => exp (I*z*y)) (exp (I*z*x)*(I*z)) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (I*z)).cexp
    have hh := he.mul ((h₁.const_mul (2*I*z)).sub
      ((((ha.differentiable (by norm_num)) x).hasDerivAt.const_mul I).mul h₂))
    convert! hh using 1
    dsimp only [P,F,Y,Φ,classicalPotentialOfFunctions,classicalScalarForcing,ContinuousMap.coe_mk,
      classicalODECoefficient_apply,Prod.fst_add,Prod.snd_add,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    simp
    ring_nf
    simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1 hP.continuousOn
    (fun x hx => (hd ⟨x,⟨hx.1.le,hx.2.le.trans t.property.2⟩⟩))
    (hF.neg.intervalIntegrable 0 t.val)
  have h0 : P 0 = 0 := by simp [P,Y]
  simp only [Pi.neg_apply] at hi
  rw [intervalIntegral.integral_neg,h0,sub_zero] at hi
  have he := congrArg (fun u : ℂ => exp (-I*z*t.val)*u) hi
  have hexp : exp (-I*z*t.val)*exp (I*z*t.val) = 1 := by rw [← exp_add]; ring_nf; simp
  dsimp only [P] at he
  rw [← mul_assoc,hexp,one_mul] at he
  change (2*I*z)*(Y t).1 = I*a t*(Y t).2-exp (-I*z*t.val)*(∫ x in (0:ℝ)..t.val, F x)
  linear_combination -he

end NLS.ZakharovShabat
