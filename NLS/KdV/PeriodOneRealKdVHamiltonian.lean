import NLS.KdV.PeriodOneHamiltonian
import NLS.ZakharovShabat.ClassicalNLSSobolevEnergy
import Mathlib.Analysis.Calculus.Deriv.Star

/-! The actual COMPLEX period-one KdV energy is real on the physical
Fourier real form of H1. No spectral or finite-gap assumption is used. -/
noncomputable section
open Set Complex NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem periodOneKdVHamiltonian_conj_eq_of_real (q : ScalarDomain 2)
    (hq : ∀ k : ℤ, q.val (-k)=(starRingEnd ℂ) (q.val k)) :
    (starRingEnd ℂ) (periodOneKdVHamiltonian q)=periodOneKdVHamiltonian q := by
  have hqC : sobolevConjugateCLM q=q := by
    apply Subtype.ext
    funext k
    rw [sobolevConjugateCLM_apply,hq,starRingEnd_self_apply]
  let f : ℝ → ℂ := fun x => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))
  have hsyn (x : ℝ) : (starRingEnd ℂ) (f x)=f x := by
    have h := periodOneSobolevSynthesis_conjugate q x
    rw [hqC] at h
    exact h.symm
  have hfun : (fun x : ℝ => star (f x))=f := funext hsyn
  have hd (x : ℝ) : (starRingEnd ℂ) (deriv f x)=deriv f x := by
    have h := deriv.star (f := f) (x := x)
    rw [hfun] at h
    exact h.symm
  rw [periodOneKdVHamiltonian_eq_integral,← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  change (starRingEnd ℂ) ((1/2:ℂ)*(deriv f x)^2+(f x)^3)=_
  have hc : (starRingEnd ℂ) (1/2:ℂ)=(1/2:ℂ) := by
    convert! Complex.conj_ofReal (1/2:ℝ) using 1 <;> norm_num
  rw [map_add,map_mul,hc,map_pow,map_pow,hd,hsyn]

theorem periodOneKdVHamiltonian_im_eq_zero_of_real (q : ScalarDomain 2)
    (hq : ∀ k : ℤ, q.val (-k)=(starRingEnd ℂ) (q.val k)) :
    (periodOneKdVHamiltonian q).im=0 := by
  have h := congrArg Complex.im (periodOneKdVHamiltonian_conj_eq_of_real q hq)
  simp only [Complex.conj_im] at h
  linarith

end NLS.KdV
