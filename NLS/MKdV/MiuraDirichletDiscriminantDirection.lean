import NLS.MKdV.MiuraDiscriminantSourceGradient

/-! # Original Dirichlet cotangents paired with actual spectral source directions -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraDirichletGradient_discriminant_difference
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (B : MiuraDirichletBranch a ha m hm) (z : ℂ) (hz : z ≠ 0) :
    reflectedHilbertPairing (scalarInclusion B.energyGradient.gradient)
      (miuraSourceDifferenceCLM (sourceDiscriminantCotangent (by simp) z (sobolevSourceInclusion (a,a)))) =
      2*z*(∫ x in (0 : ℝ)..1,
        extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) m hm) x*
        extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) (z^2)) x) := by
  have hp := miuraHillDiscriminantGradient_bracket_eq_energy_first a ha m hm B (z^2)
  rw [SobolevGardnerGradientAt.bracket,periodOneDerivative_miuraHillDiscriminantGradient,
    map_smul,smul_eq_mul] at hp
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hz)
  calc
    _ = _ := hp
    _ = _ := by ring

end NLS.MKdV
