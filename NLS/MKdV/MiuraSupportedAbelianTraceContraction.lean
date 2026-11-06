import NLS.MKdV.MiuraFiniteAbelianTraceContraction
import NLS.KdV.HillClosedDirichletAbelianValues

/-! # Abelian contraction on arbitrary finite open-gap supports

Closed non-own numerator values vanish exactly. Thus interpolation and
the interior trace contraction can be restricted to a finite support
without imposing interior-sheet hypotheses on any closed gaps between it.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSelectedAbelianPsi_supported_filled_interpolation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
    (∑ k ∈ F,ψ (hillDirichletEnergies q k)*dslope s (hillDirichletEnergies q k) E/
      deriv s (hillDirichletEnergies q k)) = ψ E := by
  let q := realSobolevMiuraHillPotential a ha
  obtain ⟨K,hFK⟩ := F.exists_nat_subset_range
  have hnK : n ≤ K := by have h := Finset.mem_range.mp (hFK hnF);omega
  have htail (k : ℕ) (hk : K ≤ k) : hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) = 0 := by
    apply hclosed k
    intro hF
    have h := Finset.mem_range.mp (hFK hF)
    omega
  have hi := miuraSelectedAbelianPsi_Dirichlet_filled_interpolation a ha n hn K hnK htail E
  apply Eq.trans ?_ hi
  apply Finset.sum_subset hFK
  intro k _ hkF
  have hkn : k+1 ≠ n := by intro he;apply hkF;convert hnF using 1;omega
  rw [hillAbelianSelectedGlobalPsi_closed_Dirichlet_eq_zero q n hn k hkn (hclosed k hkF),zero_mul,zero_div]

theorem miuraSelectedAbelianPsi_supported_trace_contraction (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (hsheet : ∀ k ∈ F,hillDirichletSheetRoot (sobolevMiuraHillPotential a)
      (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k) ≠ 0)
    (E : ℂ) (hE : ∀ k ∈ F,E ≠ (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k : ℂ)) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    (∑ k ∈ F,ψ (hillDirichletEnergies q k)*
      (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q (k+1) (by omega)) x*
        extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) E) x)/
          hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)) = -ψ E/2 := by
  let q := realSobolevMiuraHillPotential a ha
  let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
  have hi := miuraSelectedAbelianPsi_supported_filled_interpolation a ha n hn F hnF hclosed E
  change (∑ k ∈ F,ψ (hillDirichletEnergies q k)*dslope s (hillDirichletEnergies q k) E/
    deriv s (hillDirichletEnergies q k)) = ψ E at hi
  have ho : (∑ k ∈ F,ψ (hillDirichletEnergies q k)*s E/
      (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) = ψ E := by
    rw [← hi]
    apply Finset.sum_congr rfl
    intro k hk
    have hneq : E ≠ (hillDirichletEnergies q k : ℂ) := hE k hk
    rw [dslope_of_ne s hneq]
    have hz : s (hillDirichletEnergies q k) = 0 := by
      dsimp only [s]
      rw [← realSobolevMiuraHillPotential_toCoeff a ha]
      exact hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega)
    simp only [slope,vsub_eq_sub,smul_eq_mul,hz,sub_zero,div_eq_mul_inv,mul_inv_rev]
    ring
  calc
    _ = ∑ k ∈ F,-(1/2 : ℂ)*(ψ (hillDirichletEnergies q k)*s E/
        (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hr := integral_hillDirichletGradient_discriminantSpatial_sheet_resolvent q (k+1) (by omega) E (hE k hk).symm
      dsimp only at hr
      simp only [q,realSobolevMiuraHillPotential_toCoeff a ha] at hr
      rw [hr]
      have hd : deriv s (hillDirichletEnergies q k) ≠ 0 := by
        dsimp only [s]
        rw [← realSobolevMiuraHillPotential_toCoeff a ha]
        exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _
          (hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega))
      exact sheet_weighted_resolvent_cancel _ _ _ _ E _ (hsheet k hk) hd (hE k hk)
    _ = -(1/2 : ℂ)*(∑ k ∈ F,ψ (hillDirichletEnergies q k)*s E/
        (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) := (Finset.mul_sum _ _ _).symm
    _ = -ψ E/2 := by rw [ho];ring

end NLS.MKdV
