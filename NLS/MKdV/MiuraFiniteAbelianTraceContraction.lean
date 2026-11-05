import NLS.MKdV.MiuraFiniteGapAbelianInterpolation
import NLS.KdV.HillDirichletSheetNormalization

/-! # The actual trace-direction contraction of the independent Abelian differential

On an interior finite divisor the exact characteristic interpolation
contracts the original trace-gradient pairings to minus one half the
independently normalized numerator. This fixes the sign and factor of
this intermediate resolvent calculation; a phase rotation law is separate.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSelectedAbelianPsi_trace_contraction (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (hsheet : ∀ k ∈ Finset.range K,hillDirichletSheetRoot (sobolevMiuraHillPotential a)
      (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k) ≠ 0)
    (E : ℂ) (hE : ∀ k ∈ Finset.range K,E ≠ (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k : ℂ)) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    (∑ k ∈ Finset.range K,ψ (hillDirichletEnergies q k)*
      (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q (k+1) (by omega)) x*
        extend (hillDiscriminantGradientSpatialCurve (sobolevMiuraHillPotential a) E) x)/
          hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)) = -ψ E/2 := by
  let q := realSobolevMiuraHillPotential a ha
  let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
  have hinterp := miuraSelectedAbelianPsi_Dirichlet_interpolation a ha n hn K hK hclosed E hE
  calc
    _ = ∑ k ∈ Finset.range K,-(1/2 : ℂ)*
        (ψ (hillDirichletEnergies q k)*s E/
          (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hres := integral_hillDirichletGradient_discriminantSpatial_sheet_resolvent q (k+1) (by omega) E
        (hE k hk).symm
      dsimp only at hres
      simp only [q,realSobolevMiuraHillPotential_toCoeff a ha] at hres
      rw [hres]
      have hd : deriv s (hillDirichletEnergies q k) ≠ 0 := by
        dsimp only [s]
        rw [← realSobolevMiuraHillPotential_toCoeff a ha]
        exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _
          (hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega))
      change ψ (hillDirichletEnergies q k)*
        (hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)*s E/
          (2*((hillDirichletEnergies q k : ℂ)-E)*deriv s (hillDirichletEnergies q k)))/
        hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k) = _
      exact sheet_weighted_resolvent_cancel _ _ _ _ E _ (hsheet k hk) hd (hE k hk)
    _ = -(1/2 : ℂ)*(∑ k ∈ Finset.range K,ψ (hillDirichletEnergies q k)*s E/
        (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) :=
      (Finset.mul_sum _ _ _).symm
    _ = -ψ E/2 := by rw [hinterp];ring

end NLS.MKdV
