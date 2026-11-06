import NLS.KdV.HillDiscriminantNativeGradient
import NLS.KdV.HillDirichletDiscriminantMagri
import NLS.MKdV.MiuraDirichletBranchGradients

/-! # Actual original H¹ Gardner coupling of the Hill trace and Dirichlet energy

The gradients are the full complex Fréchet derivatives of the original
functionals. The contour energy factor follows from the physical weak
Magri identity, with its nonzero endpoint contribution included.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraHillDiscriminantGradient (a : ScalarDomain 2) (E : ℂ) :
    SobolevGardnerGradientAt (fun b => hillL2Discriminant (sobolevMiuraHillPotential b) E) a :=
  miuraSobolevPullbackGradient (fun p => hillL2Discriminant (Coeff.periodDouble p) E) a
    (hillDiscriminantNativeGradient (sobolevMiuraHillPotential a) E)
    (hasFDerivAt_hillDiscriminant_unit _ _ rfl E)

theorem miuraHillDiscriminantGradient_bracket
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (B : MiuraDirichletBranch a ha n hn) (E : ℂ) :
    B.energyGradient.bracket (miuraHillDiscriminantGradient a E) =
      hillDirichletDiscriminantMagriBracket (realSobolevMiuraHillPotential a ha) n hn E := by
  have h := sobolevMiuraPullbackGradient_bracket_eq_Magri _ _ a _ _
    B.unit_energy_derivative (hasFDerivAt_hillDiscriminant_unit _ _ rfl E)
  change B.energyGradient.bracket (miuraHillDiscriminantGradient a E) =
    hillSobolevMagriBivector (sobolevMiuraUnitPotential a)
      (hillDirichletNativeGradient (realSobolevMiuraHillPotential a ha) n hn)
      (hillDiscriminantNativeGradient (sobolevMiuraHillPotential a) E) at h
  rw [← realSobolevMiuraHillPotential_toCoeff a ha,
    ← realSobolevMiuraHillPotential_periodHalve a ha] at h
  rw [hillDirichletNativeGradient,hillDiscriminantNativeGradient,
    hillSobolevMagriBivector_eq_weakGradientMagri] at h
  exact h

theorem miuraHillDiscriminantGradient_bracket_eq_energy_first
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (B : MiuraDirichletBranch a ha n hn) (E : ℂ) :
    B.energyGradient.bracket (miuraHillDiscriminantGradient a E) =
      4*E*(∫ x in (0 : ℝ)..1,
        extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) n hn) x*
        extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) E) x) := by
  rw [miuraHillDiscriminantGradient_bracket a ha n hn B E,
    hillDirichletDiscriminantMagriBracket_eq_energy_first,realSobolevMiuraHillPotential_toCoeff]

end NLS.MKdV
