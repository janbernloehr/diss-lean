import NLS.MKdV.MiuraFiniteAbelianTraceContraction
import NLS.MKdV.MiuraIndependentCanonicalRoot

/-! # Actual independent Abelian interpolation and physical normalization

The finite-gap interpolation holds at every complex energy, including
all divisor nodes and closed contributing gaps. The independent canonical
root agrees with the physical Miura branch. The trace contraction has its
proved sign on an interior finite divisor; full phase rotation remains open.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.MKdV NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_Abelian_finite_gap_Dirichlet_interpolation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
    (∑ k ∈ Finset.range K,ψ (hillDirichletEnergies q k)*
      dslope s (hillDirichletEnergies q k) E/deriv s (hillDirichletEnergies q k)) = ψ E :=
  miuraSelectedAbelianPsi_Dirichlet_filled_interpolation a ha n hn K hK hclosed E

theorem independent_Abelian_physical_root_normalization (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    let q := realSobolevMiuraHillPotential a ha
    EqOn (hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2)
      (canonicalMiuraHillRoot a) (hillL2RealCutDomain q.val q.property.1 q.property.2) :=
  hillEnergyCanonicalRootProduct_eq_canonicalMiuraHillRoot a ha

theorem independent_Dirichlet_sheet_mass_normalization (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) :
    let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
    ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val) μ)^2-1)/
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) =
        hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val) μ/deriv s μ :=
  hillDirichlet_sheet_mass_ratio q n hn

theorem independent_Abelian_interior_trace_contraction (a : ScalarDomain 2)
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
        extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) E) x)/
          hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)) = -ψ E/2 :=
  miuraSelectedAbelianPsi_trace_contraction a ha n hn K hK hclosed hsheet E hE

end NLS.Articles.MKdVNLSHierarchies
