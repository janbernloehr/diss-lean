import NLS.KdV.HillGardnerEnergyContinuity
import NLS.KdV.HillGardnerAbelianAngle
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Actual Fourier contour tangents and Abelian period duality -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The normalized contour of the actual trace-gradient directions in
L2 Fourier coefficients. Identification with the gradient of the physical
action is a separate theorem; this definition assumes no action model. -/
def hillL2TracePeriodDirection (m : ℕ) : Coeff 2 :=
  -(Real.pi : ℂ)⁻¹ • ∮ E in C((hillRealGapCenter q hq hr m : ℂ),
    hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
      (hillEnergyCanonicalRootProduct q hq hr E)⁻¹ •
        hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E

theorem circleIntegrable_hillL2TracePeriodDirection_integrand (m : ℕ) (hm : 1≤m) :
    CircleIntegrable (fun E => (hillEnergyCanonicalRootProduct q hq hr E)⁻¹ •
      hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E)
      (hillRealGapCenter q hq hr m : ℂ)
      (hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m) := by
  have hR := add_nonneg (hillRealGapContour_geometry q hq hr m hm).1
    (hillRealGapContour_geometry q hq hr m hm).2.1.le
  have hs := hillRealGapContour_sphere_subset q hq hr m hm
  have hroot := (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn.mono hs
  exact (hroot.inv₀ (fun E hE => hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E (hs hE))).smul
    (continuous_hillL2DiscriminantGardnerDirection_energy (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)).continuousOn
    |>.circleIntegrable hR

/-- Pairing any continuous linear functional with the contour tangent is
the actual scalar contour of its trace-direction pairings. -/
theorem apply_hillL2TracePeriodDirection (m : ℕ) (hm : 1≤m) (L : Coeff 2 →L[ℂ] ℂ) :
    L (hillL2TracePeriodDirection q hq hr m) =
      -(Real.pi : ℂ)⁻¹ * ∮ E in C((hillRealGapCenter q hq hr m : ℂ),
        hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
        L (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E)/
          hillEnergyCanonicalRootProduct q hq hr E := by
  rw [hillL2TracePeriodDirection,map_smul,map_circleIntegral L
    (circleIntegrable_hillL2TracePeriodDirection_integrand q hq hr m hm)]
  simp only [map_smul,smul_eq_mul]
  congr 1
  congr 1
  funext E
  ring

/-- Every actual discriminant is stationary along every normalized
contour direction, including contours enclosing a closed gap. -/
theorem fderiv_hillL2Discriminant_tracePeriodDirection (m : ℕ) (hm : 1≤m) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p b) (SpectralWeight.one.toCoeff q))
      (hillL2TracePeriodDirection q hq hr m)=0 := by
  rw [apply_hillL2TracePeriodDirection q hq hr m hm]
  simp only [fderiv_hillL2Discriminant_gardnerDirection_eq_zero,zero_div]
  simp [circleIntegral]

/-- The proved raw Abelian angle derivative and the actual normalized
periods determine its exact orientation on all contour tangents. -/
theorem fderiv_hillAbelianAngle_tracePeriodDirection
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) (A : Coeff 2 → ℂ)
    (hA : ∀ b : ℂ, (fderiv ℂ A (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=
        -hillAbelianSelectedGlobalPsi q hq hr n hn b/2) :
    (fderiv ℂ A (SpectralWeight.one.toCoeff q)) (hillL2TracePeriodDirection q hq hr m)=
      if m=n then 1 else 0 := by
  rw [apply_hillL2TracePeriodDirection q hq hr m hm]
  have he : (fun E => (fderiv ℂ A (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E)/
        hillEnergyCanonicalRootProduct q hq hr E) =
      (fun E => -(1/2:ℂ)*(hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillEnergyCanonicalRootProduct q hq hr E)) := by
    funext E
    rw [hA E]
    ring
  rw [he,circleIntegral.integral_const_mul]
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn m hm
  convert hp using 1
  ring

end NLS.KdV
