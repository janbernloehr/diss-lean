import NLS.Articles.KdVPseudomeasures.OriginalHillH1ActionCurve
import NLS.KdV.PeriodOneRealKdVHamiltonian

/-! The actual complex physical H1 energy equals its real Hamiltonian,
and its derivative along the genuine action curve is the actual real
KdV frequency embedded into the complex numbers. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem hillH1_complexEnergy_eq_realEnergy (q : RealSignedHilbert (signedStepOrder 0 1)) :
    periodOneKdVHamiltonian (signedOneRealToScalarDomain q)=(hillH1KdVHamiltonian q:ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    apply periodOneKdVHamiltonian_im_eq_zero_of_real
    intro k
    rw [signedOneRealToScalarDomain_apply,signedOneRealToScalarDomain_apply]
    exact q.property k

theorem hasDerivAt_hillH1ActionCurve_complex_energy (n : ℕ+)
    (q : RealSignedHilbert (signedStepOrder 0 1))
    (hg : hillHminusCanonicalGapSquare n (hillRealMeanZeroInclusion (hillIntegerSourceInclusion 1 q))≠0) :
    HasDerivAt (fun t : ℝ => periodOneKdVHamiltonian (signedOneRealToScalarDomain (hillH1ActionCurve n q t)))
      (hillH1KdVFrequency n ((hillIntegerSobolevEquiv 1).equiv q):ℂ) 0 := by
  simpa only [hillH1_complexEnergy_eq_realEnergy] using!
    (hasDerivAt_hillH1ActionCurve_energy n q hg).ofReal_comp

end NLS.Articles.KdVPseudomeasures
