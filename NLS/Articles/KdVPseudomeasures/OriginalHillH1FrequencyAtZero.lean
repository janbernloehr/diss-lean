import NLS.Articles.KdVPseudomeasures.OriginalHillH1CanonicalPotential
import NLS.KdV.PeriodOneHamiltonianCurveJet
import NLS.KdV.PeriodOneKineticModePair
import NLS.SequenceSpaces.HalfFourierInverseNormalization

/-! The actual normalized physical KdV frequencies at zero are EXACTLY
(2*pi*n)^3. The original Hamiltonian, actual strong inverse derivative,
and physical kinetic form fix every numerical and period-one factor. -/
noncomputable section
open Complex NLS.Fourier NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem periodOneSobolevKinetic_hillH1PhysicalModeCurve_zero (n : ℕ+) :
    periodOneSobolevKinetic (deriv (hillH1PhysicalModeCurve n) 0,deriv (hillH1PhysicalModeCurve n) 0)=
      ((2*(2*Real.pi*(n:ℕ))^3:ℝ):ℂ) := by
  have hn : (n:ℤ)≠-(n:ℤ) := by
    have hpos : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  have hv (k : ℤ) : (deriv (hillH1PhysicalModeCurve n) 0).val k=
      (if k=(n:ℤ) then halfFourierInverseSymbol (n:ℤ) else 0)+
        (if k=-(n:ℤ) then halfFourierInverseSymbol (n:ℤ) else 0) := by
    rw [deriv_hillH1PhysicalModeCurve_zero_apply]
    by_cases hk : k=(n:ℤ)
    · subst k; simp [hn]
    · by_cases hm : k=-(n:ℤ)
      · subst k; simp [Ne.symm hn,halfFourierInverseSymbol_neg]
      · simp [hk,hm]
  rw [periodOneSobolevKinetic_mode_pair _ n _ hv,halfFourierInverseSymbol_positive_sq]
  push_cast
  ring

theorem hasDerivAt_hillH1Canonical_mode_energy (n : ℕ+) (t : ℝ) :
    HasDerivAt (fun s : ℝ => hillH1CanonicalHamiltonian (s • hillH1ModeCLM n 1))
      (2*t*hillH1KdVFrequency n (t • hillH1ModeCLM n 1)) t := by
  have hd := @hasDerivAt_differentiable_real_line
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    hillH1CanonicalHamiltonian 0 (hillH1ModeCLM n 1) t
    (analyticAt_hillH1CanonicalHamiltonian _).differentiableAt
  simp only [zero_add] at hd
  have hv : (t • hillH1ModeCLM n 1).val.val.val (n:ℤ)=(t:ℂ) := by
    have hn : (n:ℤ)≠-(n:ℤ) := by
      have hpos : (0:ℤ)<n := by exact_mod_cast n.pos
      omega
    change (t:ℂ)*(hillH1ModeCLM n 1).val.val.val (n:ℤ)=_
    rw [hillH1ModeCLM_apply]
    simp [hn]
  have hgrad : (fderiv ℝ hillH1CanonicalHamiltonian (t • hillH1ModeCLM n 1)) (hillH1ModeCLM n 1)=
      2*t*hillH1KdVFrequency n (t • hillH1ModeCLM n 1) := by
    rw [hillH1CanonicalHamiltonian_mode_gradient,hv,Complex.conj_ofReal,mul_one,Complex.ofReal_re]
    ring
  rw [hgrad] at hd
  exact hd

theorem hillH1KdVFrequency_zero (n : ℕ+) : hillH1KdVFrequency n 0=(2*Real.pi*(n:ℕ))^3 := by
  let q := hillH1PhysicalModeCurve n
  let v := fun t : ℝ => (periodOneSobolevKinetic (q t,deriv q t)+
    periodOneCircleMean (3*(periodOneSobolevSynthesis (q t))^2*periodOneSobolevSynthesis (deriv q t))).re
  have hv (t : ℝ) : v t=2*t*hillH1KdVFrequency n (t • hillH1ModeCLM n 1) := by
    have hd := hasDerivAt_periodOneKdV_real_curve q t (analyticAt_hillH1PhysicalModeCurve n t).differentiableAt
    change HasDerivAt (fun s : ℝ => hillH1CanonicalHamiltonian (s • hillH1ModeCLM n 1)) (v t) t at hd
    exact hd.unique (hasDerivAt_hillH1Canonical_mode_energy n t)
  have hj := hasDerivAt_periodOneKdV_real_curve_variation_zero q
    (analyticAt_hillH1PhysicalModeCurve n 0) (hillH1PhysicalModeCurve_zero n)
  change HasDerivAt v (periodOneSobolevKinetic (deriv q 0,deriv q 0)).re 0 at hj
  have hvfun : v=(fun t : ℝ => 2*t*hillH1KdVFrequency n (t • hillH1ModeCLM n 1)) := funext hv
  rw [hvfun] at hj
  have hline : AnalyticAt ℝ (fun t : ℝ => t • hillH1ModeCLM n 1) 0 := analyticAt_id.smul analyticAt_const
  have hw : AnalyticAt ℝ (fun t : ℝ => hillH1KdVFrequency n (t • hillH1ModeCLM n 1)) 0 :=
    (analyticAt_hillH1KdVFrequency n 0).comp_of_eq hline (by simp)
  have hp := ((hasDerivAt_id (0:ℝ)).const_mul 2).mul hw.differentiableAt.hasDerivAt
  have hp' : HasDerivAt (fun t : ℝ => 2*t*hillH1KdVFrequency n (t • hillH1ModeCLM n 1))
      (2*hillH1KdVFrequency n 0) 0 := by
    simpa only [id_eq,zero_smul,mul_one,mul_zero,zero_mul,add_zero] using! hp
  have he := hj.unique hp'
  change (periodOneSobolevKinetic (deriv (hillH1PhysicalModeCurve n) 0,deriv (hillH1PhysicalModeCurve n) 0)).re=
    2*hillH1KdVFrequency n 0 at he
  rw [periodOneSobolevKinetic_hillH1PhysicalModeCurve_zero,Complex.ofReal_re] at he
  linarith

end NLS.Articles.KdVPseudomeasures
