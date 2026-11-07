import NLS.KdV.HillPeriodOneL1Comparison
import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.AbsoluteContinuousCoefficients

/-! Finite source potentials have their ACTUAL differentiable physical
unit-period representatives. This is ordinary finite Fourier support,
not the unrelated finite-gap spectral condition. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

theorem contDiff_one_finiteHillPolynomial (a : ℤ →₀ ℂ) : ContDiff ℝ 1 (polynomial a) := by
  classical
  change ContDiff ℝ 1 (fun x => ∑ n ∈ a.support, a n*wave (2*n) x)
  exact ContDiff.sum (fun n _ => contDiff_const.mul (contDiff_wave (2*n)))

theorem hasDerivAt_finiteHillPotentialCurve (a : ℤ →₀ ℂ) (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (extend (periodOneL1PotentialCurve (Coeff.ofFinsupp a))) (deriv (polynomial a) x) x := by
  have he : extend (periodOneL1PotentialCurve (Coeff.ofFinsupp a)) =ᶠ[nhds x] polynomial a := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    rw [extend_coe _ ⟨y,hy.1.le,hy.2.le⟩,periodOneL1PotentialCurve_apply,periodOneSynthesis_ofFinsupp]
  exact (((contDiff_one_finiteHillPolynomial a).differentiable (by norm_num)) x).hasDerivAt.congr_of_eventuallyEq he

theorem periodOneL1PotentialCurve_endpoints (a : Coeff 1) :
    extend (periodOneL1PotentialCurve a) 1=extend (periodOneL1PotentialCurve a) 0 := by
  rw [extend_coe _ ⟨1,by constructor <;> norm_num⟩,extend_coe _ ⟨0,by constructor <;> norm_num⟩,
    periodOneL1PotentialCurve_apply,periodOneL1PotentialCurve_apply]
  simpa only [zero_add] using periodOneSynthesis_periodic a 0

end NLS.KdV
