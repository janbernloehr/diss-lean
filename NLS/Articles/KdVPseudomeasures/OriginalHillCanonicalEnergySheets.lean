import NLS.Articles.KdVPseudomeasures.OriginalHillComplexProducts
import NLS.KdV.HillCanonicalEnergyLoopPeriods

/-! Intrinsic physical energy sheets and normalized differentials for
source 3.2. One joint energy/source domain works before ALL numerator
indices. The physical sign and exact one-over-two-pi cycle periods are
preserved. This does not yet construct the Abelian phases. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_canonical_energy_sheet_and_differentials :
    IsOpen hillHminusCanonicalEnergyRootDomain ∧
      IsOpen hillHminusEnergySheetSource ∧ IsConnected hillHminusEnergySheetSource ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusEnergySheetSource) ∧
      hillHminusCanonicalEnergyRootDomain ⊆ univ ×ˢ hillHminusEnergySheetSource ∧
      hillHminusEnergySheetSource ⊆ hillHminusSimpleZeroSequenceDomain ∧
      AnalyticOnNhd ℂ hillHminusCanonicalEnergyRoot hillHminusCanonicalEnergyRootDomain ∧
      (∀ t ∈ hillHminusCanonicalEnergyRootDomain,
        hillHminusCanonicalEnergyRoot t ≠ 0 ∧ hillHminusCanonicalEnergyRoot t^2 = hillHminusRadicand t.2 t.1) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalEnergyDifferential n) hillHminusCanonicalEnergyRootDomain := by
  exact ⟨isOpen_hillHminusCanonicalEnergyRootDomain,isOpen_hillHminusEnergySheetSource,
    isConnected_hillHminusEnergySheetSource,
    (fun q => real_mem_hillHminusEnergySheetSource _ (originalPeriodOneCoefficients_real q)),
    hillHminusCanonicalEnergyRootDomain_subset_sheetSource,hillHminusEnergySheetSource_subset_simpleDomain,
    analyticOnNhd_hillHminusCanonicalEnergyRoot,
    (fun t ht => ⟨hillHminusCanonicalEnergyRoot_ne_zero t ht,hillHminusCanonicalEnergyRoot_sq t ht⟩),
    analyticOnNhd_hillHminusCanonicalEnergyDifferential⟩

theorem original_Hill_canonical_energy_sheet_physical_sign (q : OriginalHminusOnePotential)
    (E : ℂ) (hE : E.im ≠ 0) :
    (E,originalPeriodOneCoefficients q) ∈ hillHminusCanonicalEnergyRootDomain ∧
      hillHminusCanonicalEnergyRoot (E,originalPeriodOneCoefficients q) =
        hillHminusContinuedRoot (E,originalPeriodOneCoefficients q) ∧
      ∀ n : ℕ+, hillHminusCanonicalEnergyDifferential n (E,originalPeriodOneCoefficients q) =
        hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)/
          hillHminusContinuedRoot (E,originalPeriodOneCoefficients q) := by
  have hr := originalPeriodOneCoefficients_real q
  exact ⟨nonreal_mem_hillHminusCanonicalEnergyRootDomain E hE _ hr,
    hillHminusCanonicalEnergyRoot_eq_physical_of_real E hE _ hr,
    fun n => hillHminusCanonicalEnergyDifferential_eq_physical_of_real n E hE _ hr⟩

theorem original_Hill_canonical_energy_compact_complex_transport
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (q : OriginalHminusOnePotential)
    (K : Set ℂ) (hK : IsCompact K)
    (hbase : ∀ E ∈ K, (E,originalPeriodOneCoefficients q) ∈ B.energyDomain A) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball (originalPeriodOneCoefficients q) r, ∀ E ∈ K,
      (E,y) ∈ hillHminusCanonicalEnergyRootDomain ∧ (E,y) ∈ B.energyDomain A ∧
      hillHminusCanonicalEnergyRoot (E,y) = B.energyRoot (E,y) ∧
      ∀ n : ℕ+, hillHminusCanonicalEnergyDifferential n (E,y) = B.energyDifferential A n (E,y) :=
  exists_uniform_canonical_energy_compact_transport B A _ (originalPeriodOneCoefficients_real q) K hK hbase

theorem original_Hill_canonical_energy_cycle_complex_periods
    (P : HillProductEquationPatch) (q : OriginalHminusOnePotential)
    (hq : originalPeriodOneCoefficients q ∈ P.source) (m : ℕ+) :
    ∃ r : ℝ, 0 < r ∧ ball (originalPeriodOneCoefficients q) r ⊆ hillHminusEnergySheetSource ∧
      ∀ y ∈ ball (originalPeriodOneCoefficients q) r,
        (P.energyLoop m).Inside {E | (E,y) ∈ hillHminusCanonicalEnergyRootDomain} ∧
        ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*(P.energyLoop m).integral
          (fun E => hillHminusCanonicalEnergyDifferential n (E,y)) = if m = n then 1 else 0 :=
  P.exists_canonical_energyLoop_complex_period_ball _ hq (originalPeriodOneCoefficients_real q) m

end NLS.Articles.KdVPseudomeasures
