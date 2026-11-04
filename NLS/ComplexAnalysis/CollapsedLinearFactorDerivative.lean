import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Derivatives under a quadratic energy pullback and at a collapsed
linear factor. The quotient is never divided by its vanishing factor. -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

theorem hasDerivAt_comp_quadratic_shift (f : ℂ → ℂ) (z c d : ℂ)
    (hf : HasDerivAt f d (z^2-c)) :
    HasDerivAt (fun w => f (w^2-c)) (d*(2*z)) z := by
  have hg : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa using! ((hasDerivAt_id z).pow 2).sub_const c
  exact hf.comp z hg

theorem deriv_eq_of_collapsed_linear_factor (F E K : ℂ → ℂ) (τ : ℂ)
    (hE : DifferentiableAt ℂ E τ) (hK : DifferentiableAt ℂ K τ)
    (he : F =ᶠ[𝓝 τ] fun z => E z*(τ-z)*K z) :
    deriv F τ = -E τ*K τ := by
  have hd := ((hE.hasDerivAt.mul ((hasDerivAt_id τ).const_sub τ)).mul hK.hasDerivAt)
  have hpoly : HasDerivAt (fun z => E z*(τ-z)*K z) (-E τ*K τ) τ := by
    simpa only [id_eq,Pi.mul_apply,sub_self,mul_zero,zero_mul,zero_add,add_zero,mul_one,mul_neg,zero_sub] using! hd
  exact (hpoly.congr_of_eventuallyEq he).deriv


variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_square_energy_apply (f g : A → ℂ) (x h : A) (c : ℂ)
    (hf : DifferentiableAt ℂ f x) (he : g =ᶠ[𝓝 x] fun q => f q^2-c) :
    (fderiv ℂ g x) h=2*f x*((fderiv ℂ f x) h) := by
  have hd := ((hf.hasFDerivAt.pow 2).sub_const c).fderiv
  change fderiv ℂ (fun q => f q^2-c) x = _ at hd
  rw [he.fderiv_eq,hd]
  simp only [smul_apply,smul_eq_mul]
  ring

theorem fderiv_div_apply_of_zero (f g : A → ℂ) (x h : A)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (hf0 : f x=0) (hgne : g x ≠ 0) :
    (fderiv ℂ (fun q => f q/g q) x) h=((fderiv ℂ f x) h)/g x := by
  have hi := (hasFDerivAt_inv hgne).comp x hg.hasFDerivAt
  have hd := (hf.hasFDerivAt.fun_mul hi).fderiv
  change fderiv ℂ (fun q => f q*(g q)⁻¹) x = _ at hd
  rw [show (fun q => f q/g q) = (fun q => f q*(g q)⁻¹) by funext q; exact div_eq_mul_inv _ _]
  rw [hd]
  simp only [Function.comp_def,add_apply,smul_apply,smul_eq_mul,hf0,zero_mul,zero_add]
  ring

theorem fderiv_three_factors_apply_of_middle_zero (f g k : A → ℂ) (x h : A)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (hk : DifferentiableAt ℂ k x) (hg0 : g x=0) :
    (fderiv ℂ (fun q => f q*g q*k q) x) h = f x*((fderiv ℂ g x) h)*k x := by
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt |>.fun_mul hk.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hg0,mul_zero,zero_mul,zero_add,add_zero]
  ring

theorem fderiv_mul_apply_of_left_zero (f g : A → ℂ) (x h : A)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) (hf0 : f x=0) :
    (fderiv ℂ (fun q => f q*g q) x) h = ((fderiv ℂ f x) h)*g x := by
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hf0,zero_mul,zero_add]
  ring

theorem fderiv_mul_apply_of_right_zero (f g : A → ℂ) (x h : A)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) (hg0 : g x=0) :
    (fderiv ℂ (fun q => f q*g q) x) h = f x*((fderiv ℂ g x) h) := by
  rw [(hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,hg0,zero_mul,add_zero]

end NLS.ComplexAnalysis
