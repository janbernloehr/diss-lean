import NLS.Articles.KdVPseudomeasures.OriginalHillUniformDiagonalCorrection
import NLS.KdV.HillActionAngleEnergyDomain

/-! The Section 5 ACTUAL scalar Cartesian formulas satisfy the
source3.2(ii) ORIGINAL-energy spectral estimate on a common native
complex neighborhood of the entire real form, BEFORE ALL n.
Target sequence mapping and Gardner canonicality remain separate. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_Cartesian_energy_estimate_common_domain :
    IsOpen hillHminusActionAngleEnergyDomain ∧ IsConnected hillHminusActionAngleEnergyDomain ∧
      (∀ q : OriginalHminusOnePotential,
        originalPeriodOneCoefficients q ∈ hillHminusActionAngleEnergyDomain) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusActionAngleX n) hillHminusActionAngleEnergyDomain ∧
        AnalyticOnNhd ℂ (hillHminusActionAngleY n) hillHminusActionAngleEnergyDomain) :=
  ⟨isOpen_hillHminusActionAngleEnergyDomain,isConnected_hillHminusActionAngleEnergyDomain,
    (fun q => real_mem_hillHminusActionAngleEnergyDomain _ (originalPeriodOneCoefficients_real q)),
    analyticOnNhd_hillHminusActionAngle_on_energy_domain⟩

theorem original_Hill_Cartesian_energy_estimate_UNIFORM_ALL_n :
    ∀ q ∈ hillHminusActionAngleEnergyDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleEnergyDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionAngleFactorPlus n a‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a ∧
        ‖hillHminusActionAngleFactorMinus n a‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a ∧
        ‖hillHminusActionAngleX n a‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a ∧
        ‖hillHminusActionAngleY n a‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n a :=
  exists_locally_uniform_actionAngle_original_energy_bound

theorem original_Hill_Cartesian_energy_estimate_real (q : OriginalHminusOnePotential) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ hillHminusActionAngleEnergyDomain ∧ ∃ C : ℝ, 0 < C ∧
      ∀ a : OriginalHminusOnePotential, originalPeriodOneCoefficients a ∈ U → ∀ n : ℕ+,
        let y := originalPeriodOneCoefficients a
        let hr := originalPeriodOneCoefficients_real a
        let W := (hillHminusLabels y hr (2*(n:ℕ))-hillHminusLabels y hr (2*(n:ℕ)-1))+
          |hillHminusDirichletLabels y hr n-
            (hillHminusLabels y hr (2*(n:ℕ)-1)+hillHminusLabels y hr (2*(n:ℕ)))/2|
        ‖hillHminusActionAngleX n y‖ ≤ (C/Real.sqrt (n:ℕ))*W ∧
          ‖hillHminusActionAngleY n y‖ ≤ (C/Real.sqrt (n:ℕ))*W := by
  obtain ⟨U,hU,hqU,hUD,C,hC,hbound⟩ := exists_locally_uniform_actionAngle_original_energy_bound
    (originalPeriodOneCoefficients q)
    (real_mem_hillHminusActionAngleEnergyDomain _ (originalPeriodOneCoefficients_real q))
  refine ⟨U,hU,hqU,hUD,C,hC,?_⟩
  intro a ha n
  have h := hbound (originalPeriodOneCoefficients a) ha n
  rw [hillHminusCanonicalCartesianWeight_eq_real n _ (originalPeriodOneCoefficients_real a)] at h
  exact ⟨h.2.2.1,h.2.2.2⟩

end NLS.Articles.KdVPseudomeasures
