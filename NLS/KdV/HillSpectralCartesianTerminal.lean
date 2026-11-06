import NLS.KdV.HillSpectralCartesian

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDirichletCirclePhase_eq_exp_of_terminal (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) (θ : ℝ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr n) (hillRealGapHalfLength q hq hr n) (θ : ℂ) =
      (hillDirichletEnergy q hq hr n hn : ℂ))
    (hsin : Complex.sin (θ : ℂ) = hillDirichletGapSine q hq hr n hn) :
    hillDirichletCirclePhase q hq hr n hn = Complex.exp (((θ : ℂ)-(Real.pi : ℂ))*I) := by
  have hδ : (hillRealGapHalfLength q hq hr n : ℂ) ≠ 0 := ofReal_ne_zero.mpr hgap
  have hcos : Complex.cos (θ : ℂ) = hillDirichletGapCosine q hq hr n hn := by
    apply (eq_div_iff hδ).mpr
    unfold cosineGapPoint at hpoint
    linear_combination hpoint
  rw [sub_mul,Complex.exp_sub,Complex.exp_pi_mul_I,div_neg,div_one,
    Complex.exp_mul_I,hillDirichletCirclePhase,← hcos,← hsin]
  ring

theorem hillSpectralCartesian_eq_abelian_terminal (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength q hq hr n ≠ 0) (θ : ℝ)
    (hpoint : cosineGapPoint (hillRealGapCenter q hq hr n) (hillRealGapHalfLength q hq hr n) (θ : ℂ) =
      (hillDirichletEnergy q hq hr n hn : ℂ))
    (hsin : Complex.sin (θ : ℂ) = hillDirichletGapSine q hq hr n hn) :
    hillSpectralCartesian q hq hr n hn = (Real.sqrt (2*hillRealGapIntegral q hq hr n 0) : ℂ)*
      Complex.exp (I*((θ : ℂ)-(Real.pi : ℂ)+hillSummedRegularAbelianCorrection q hq hr n hn)) := by
  rw [hillSpectralCartesian,hillDirichletCirclePhase_eq_exp_of_terminal q hq hr n hn hgap θ hpoint hsin]
  rw [show I*((θ : ℂ)-(Real.pi : ℂ)+hillSummedRegularAbelianCorrection q hq hr n hn) =
    ((θ : ℂ)-(Real.pi : ℂ))*I+I*hillSummedRegularAbelianCorrection q hq hr n hn by ring,Complex.exp_add]
  ring

end NLS.KdV
