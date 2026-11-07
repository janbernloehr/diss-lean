import NLS.KdV.ClassicalKdVJet
import NLS.KdV.HillEnergyDiscriminantGradients
import NLS.KdV.HillIsospectralData
import NLS.KdV.HillRealActionContinuity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
namespace NLS.KdV

/-- The physical KdV PDE in its original Fourier L² topology. At each time
the spatial jet gives actual derivatives, and the time derivative is the
Fourier realization of 6*q*q_x-q_xxx. No isospectral condition is assumed. -/
def IsClassicalKdVTrajectory (u : ℝ → RealPeriodOneHillPotential) : Prop :=
  ∀ t, ∃ J : PeriodicKdVJet,
    SpectralWeight.one.toCoeff (u t).val = SpectralWeight.one.toCoeff J.coefficients ∧
    HasDerivAt (fun τ => SpectralWeight.one.toCoeff (u τ).val)
      (SpectralWeight.one.toCoeff J.velocityCoefficients) t

theorem IsClassicalKdVTrajectory.mean_derivative_zero
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) (t : ℝ) :
    HasDerivAt (fun τ => (u τ).val.val 0) 0 t := by
  obtain ⟨J,_,hdt⟩ := hu t
  let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).restrictScalars ℝ
  have heval (q : Coeff 2) : L q = q 0 := rfl
  have hd := L.hasFDerivAt.comp_hasDerivAt t hdt
  have hd0 : HasDerivAt (fun τ => (u τ).val.val 0) (J.velocityCoefficients.val 0) t := by
    simpa only [Function.comp_def,heval,SpectralWeight.toCoeff_apply] using hd
  exact J.velocity_mean_zero ▸ hd0

theorem IsClassicalKdVTrajectory.mean_conserved
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) (s t : ℝ) :
    (u t).val.val 0 = (u s).val.val 0 :=
  isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun τ _ => (hu.mean_derivative_zero τ).differentiableAt.differentiableWithinAt)
    (fun τ _ => (hu.mean_derivative_zero τ).deriv) (mem_univ t) (mem_univ s)

theorem IsClassicalKdVTrajectory.discriminant_derivative_zero
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) (t : ℝ) (E : ℂ) :
    HasDerivAt (fun τ => hillL2Discriminant (SpectralWeight.one.toCoeff (u τ).val) E) 0 t := by
  obtain ⟨J,hJ,hdt⟩ := hu t
  have hD : DifferentiableAt ℂ (fun q : Coeff 2 => hillL2Discriminant q E)
      (SpectralWeight.one.toCoeff (u t).val) :=
    ((analyticOnNhd_hillL2Discriminant_joint (E,SpectralWeight.one.toCoeff (u t).val) (mem_univ _)).comp
      (f := fun q : Coeff 2 => (E,q)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hd := (hD.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hdt
  have hz : (fderiv ℂ (fun q : Coeff 2 => hillL2Discriminant q E)
      (SpectralWeight.one.toCoeff (u t).val)) (SpectralWeight.one.toCoeff J.velocityCoefficients) = 0 := by
    rw [hJ,hillEnergyDiscriminantGradient_represents_potential]
    exact J.discriminant_stationary (Complex.sqrt E)
  exact hz ▸ hd

/-- The Lax invariant is obtained from the PDE and the proved local flux,
at every energy including zero and all collapsed spectral gaps. -/
theorem IsClassicalKdVTrajectory.discriminant_conserved
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) (s t : ℝ) (E : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff (u t).val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff (u s).val) E := by
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun τ _ => (hu.discriminant_derivative_zero τ E).differentiableAt.differentiableWithinAt)
    (fun τ _ => (hu.discriminant_derivative_zero τ E).deriv) (mem_univ t) (mem_univ s)

/-- Conservation of the actual physical gap action, rather than a chosen
coordinate norm, for every classical physical KdV trajectory. -/
theorem IsClassicalKdVTrajectory.physical_actions_conserved
    {u : ℝ → RealPeriodOneHillPotential} (hu : IsClassicalKdVTrajectory u) (s t : ℝ) (n : ℕ) :
    hillRealGapIntegral (u t).val (u t).property.1 (u t).property.2 n 0 =
      hillRealGapIntegral (u s).val (u s).property.1 (u s).property.2 n 0 :=
  hillRealGapIntegral_eq_of_discriminant_eq (u t) (u s) (hu.discriminant_conserved s t) n 0

end NLS.KdV
