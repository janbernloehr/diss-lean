import NLS.Poisson.HminusGardnerWeightedEvolution
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson
local notation "Hminus" => WeightedCoeff (Weight.sobolev (-1)) 2

/-- The normalized actual bracket is stationary under an action
Hamiltonian whenever its two factors have the exact Hamiltonian rotation
laws and their entire differential identities. -/
theorem hminusGardnerBracket_normalized_hamiltonian_derivative_zero
    (F G J : Hminus → ℂ) (q : Hminus) (α β : ℂ)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hJ : AnalyticAt ℂ J q)
    (hFn : F q ≠ 0) (hGn : G q ≠ 0)
    (hFV : hminusGardnerBracket F J q = α * F q)
    (hGV : hminusGardnerBracket G J q = β * G q)
    (hFJ : fderiv ℂ (hminusGardnerBracket F J) q = α • fderiv ℂ F q)
    (hGJ : fderiv ℂ (hminusGardnerBracket G J) q = β • fderiv ℂ G q) :
    (fderiv ℂ (fun a => hminusGardnerBracket F G a / (F a * G a)) q)
      (gardnerHamiltonianVector J q) = 0 := by
  have hB : AnalyticAt ℂ (hminusGardnerBracket F G) q :=
    (gardnerBivector.analyticAt_bilinear _).comp₂
      ((hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hp := hF.differentiableAt.hasFDerivAt.mul hG.differentiableAt.hasFDerivAt
  have hi := (hasDerivAt_inv (mul_ne_zero hFn hGn)).comp_hasFDerivAt q hp
  have hd := hB.differentiableAt.hasFDerivAt.mul hi
  change (fderiv ℂ (fun a => hminusGardnerBracket F G a * (F a * G a)⁻¹) q)
    (gardnerHamiltonianVector J q) = 0
  change HasFDerivAt (fun a => hminusGardnerBracket F G a * (F a * G a)⁻¹) _ q at hd
  have hE := hminusGardnerBracket_weighted_hamiltonian_derivative F G J q α β hF hG hJ hFJ hGJ
  rw [hd.fderiv]
  simp only [smul_apply,smul_eq_mul,add_apply,Function.comp_def,Pi.mul_apply,
    fderiv_apply_gardnerHamiltonianVector,hFV,hGV,hE]
  field_simp [hFn,hGn]
  ring

end NLS.Poisson
