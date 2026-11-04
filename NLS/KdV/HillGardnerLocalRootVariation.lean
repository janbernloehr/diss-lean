import NLS.KdV.HillL2GardnerSpectralStationarity

/-! # Actual Gardner variation of local Hill radicand roots

Differentiating the actual radicand identity works for every locally
nonvanishing analytic square-root choice, without requiring the energy to
lie in the straight-source continuation domain.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem fderiv_hillL2Radicand_gardnerDirection_eq_zero
    (q : Coeff 2) (E b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
      (hillL2DiscriminantGardnerDirection q b)=0 := by
  have hA : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q :=
    (analyticOnNhd_hillL2Discriminant_joint (E,q) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hD := hA.differentiableAt.hasFDerivAt
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b))
    ((hD.mul hD).sub_const 4).fderiv
  have heq : (fun p : Coeff 2 => hillL2Discriminant p E*hillL2Discriminant p E-4)=
      (fun p => hillL2Radicand p E) := by
    funext p
    simp only [hillL2Radicand,pow_two]
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E*hillL2Discriminant p E-4) q) _ = _ at hd
  rw [heq] at hd
  simp only [add_apply,smul_apply,smul_eq_mul] at hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
    (hillL2DiscriminantGardnerDirection q b)=
      hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
        (hillL2DiscriminantGardnerDirection q b))+
      hillL2Discriminant q E*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
        (hillL2DiscriminantGardnerDirection q b)) at hd
  rw [fderiv_hillL2Discriminant_gardnerDirection_eq_zero,mul_zero,add_zero] at hd
  exact hd

/-- Every actual differentiable local nonzero radicand root is stationary
along the constructed Hill trace direction; no root derivative is assumed. -/
theorem fderiv_hillL2RadicandRoot_gardnerDirection_eq_zero
    (q : Coeff 2) (E b : ℂ) (R : Coeff 2 → ℂ)
    (hR : DifferentiableAt ℂ R q) (hne : R q≠0)
    (hsq : ∀ᶠ p in 𝓝 q, R p^2=hillL2Radicand p E) :
    (fderiv ℂ R q) (hillL2DiscriminantGardnerDirection q b)=0 := by
  have heq : (fun p : Coeff 2 => R p*R p) =ᶠ[𝓝 q] (fun p => hillL2Radicand p E) := by
    filter_upwards [hsq] with p hp
    simpa only [pow_two] using hp
  have hd := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b)) heq.fderiv_eq
  have hdR := (hR.hasFDerivAt.mul hR.hasFDerivAt).fderiv
  change fderiv ℂ (fun p : Coeff 2 => R p*R p) q = _ at hdR
  rw [hdR] at hd
  simp only [add_apply,smul_apply,smul_eq_mul] at hd
  change R q*((fderiv ℂ R q) (hillL2DiscriminantGardnerDirection q b))+
      R q*((fderiv ℂ R q) (hillL2DiscriminantGardnerDirection q b))=
      (fderiv ℂ (fun p : Coeff 2 => hillL2Radicand p E) q)
        (hillL2DiscriminantGardnerDirection q b) at hd
  rw [fderiv_hillL2Radicand_gardnerDirection_eq_zero] at hd
  have hzero : R q*((fderiv ℂ R q) (hillL2DiscriminantGardnerDirection q b))=0 := by
    linear_combination hd/2
  exact (mul_eq_zero.mp hzero).resolve_left hne

end NLS.KdV
