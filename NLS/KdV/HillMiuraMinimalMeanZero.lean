import NLS.SequenceSpaces.PeriodOneMiuraKernelAC
import NLS.FunctionalAnalysis.PeriodicScalarACMean
import NLS.KdV.HillHminusOneWeakFormReality

/-! # Actual least-energy rough Miura factors have zero mean

The nonzero literal Fourier kernel reconstructs a periodic AC solution.
Its physically real coefficient has zero integral by the integrating
factor identity. Thus the factor has zero central Fourier coefficient.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.FunctionalAnalysis

theorem mean_zero_of_periodOneMiura_kernel (u : PeriodOneRealL2) (v : Coeff 2) (hv : v ≠ 0)
    (hker : ∀ j : ℤ, 2*I*(Real.pi : ℂ)*j*v j+2*(periodOneMiuraProduct u.val v).val j = 0) :
    u.val 0 = 0 := by
  obtain ⟨F,_hFc,hFa,_hrep,hperiod,hnon,hFd⟩ := exists_periodOneMiura_kernel_AC u.val v hv hker
  let U := unitL2SynthesisEquiv u.val
  have hstar : star U = U := unitL2Synthesis_star_eq_self_of_real u.val u.property
  have hreal : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), U x = ((U x).re : ℂ) := by
    have hs := Lp.coeFn_star U
    rw [hstar] at hs
    filter_upwards [hs] with x hx
    have hi := congrArg Complex.im hx
    change (U x).im = -(U x).im at hi
    apply Complex.ext
    · rfl
    · simp only [ofReal_im]
      linarith
  have hUi : IntervalIntegrable (fun x => U x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((Lp.memLp U).integrable (by norm_num))
  let α : ℝ → ℝ := fun x => -2*(U x).re
  have hUr : IntervalIntegrable (fun x => (U x).re) volume 0 1 := ⟨hUi.1.re,hUi.2.re⟩
  have hα : IntervalIntegrable α volume 0 1 := hUr.const_mul (-2 : ℝ)
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt F ((α x : ℂ)*F x) x := by
    filter_upwards [hFd,hreal] with x hx hr
    convert hx using 1
    change ((-2*(U x).re : ℝ) : ℂ)*F x = (-2 : ℂ)*U x*F x
    rw [hr]
    push_cast
    simp only [ofReal_re]
  have hαmean := integral_eq_zero_of_nonzero_periodic_scalar_AC α hα F hFa hd hperiod hnon
  have hc : unitFourierCoefficient U 0 = u.val 0 := by
    rw [unitFourierCoefficient_eq_intervalFourierCoefficient]
    exact unitL2SynthesisLinear_coefficient u.val 0
  simp only [unitFourierCoefficient,mul_zero,neg_zero,wave_zero,mul_one] at hc
  have hre := Complex.reCLM.intervalIntegral_comp_comm hUi
  change (∫ x in (0 : ℝ)..1, (U x).re) = (∫ x in (0 : ℝ)..1, U x).re at hre
  rw [hc] at hre
  have hzeroRe : (u.val 0).re = 0 := by
    change (∫ x in (0 : ℝ)..1, (-2 : ℝ)*(U x).re) = 0 at hαmean
    rw [intervalIntegral.integral_const_mul,hre] at hαmean
    linarith
  apply Complex.ext
  · simpa only [zero_re] using hzeroRe
  · have hz := u.property 0
    simp only [neg_zero] at hz
    have hi := congrArg Complex.im hz
    simp only [conj_im] at hi
    simp only [zero_im]
    linarith

theorem mean_zero_of_minimal_realMiura_factor
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (e : ℝ) (u : PeriodOneRealL2)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hmin : ∀ (f : ℝ) (w : PeriodOneRealL2),
      periodOneMiura w.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f) :
    u.val 0 = 0 := by
  obtain ⟨v,hv,hker⟩ := exists_periodOneMiura_kernel_of_minimal q hr e u hu hmin
  exact mean_zero_of_periodOneMiura_kernel u v hv hker

/-- EVERY real mean-zero rough source has an ACTUAL real MEAN-ZERO L2
factor at its LEAST admissible energy, with the literal corrected Miura
equation and its exact squared-norm energy. No ground factor is assumed. -/
theorem exists_periodOneMiura_minimal_meanZero_factor (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ∃ e : ℝ, 0 ≤ e ∧ ∃ u : PeriodOneRealL2, u.val 0 = 0 ∧
      periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∧
      ‖u.val‖^2 = e ∧
      q = periodOneMiura u.val-periodOneL2Inclusion (lp.single 2 0 (‖u.val‖^2 : ℝ)) ∧
      ∀ (f : ℝ) (w : PeriodOneRealL2),
        periodOneMiura w.val = q+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)) → e ≤ f := by
  obtain ⟨e,he,u,hu,hnorm,hmin⟩ := exists_periodOneMiura_minimal_energy q hr hm
  refine ⟨e,he,u,mean_zero_of_minimal_realMiura_factor q hr e u hu hmin,hu,hnorm,?_,hmin⟩
  rw [hnorm,hu,add_sub_cancel_right]

end NLS.KdV
