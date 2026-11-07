import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalAbelianDivisor
import NLS.KdV.HillCanonicalPhysicalAbelianValue

/-! Intrinsic physical off-index Abelian divisor values retain the
original Hill energy and norming sheet. ONE open connected complex
native source domain contains the ENTIRE original real domain and
works BEFORE ALL indices. This does not construct the on-index angle
or sum the infinitely many off-index contributions. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_intrinsic_physical_Abelian_domain :
    IsOpen hillHminusPhysicalAbelianDomain ∧ IsConnected hillHminusPhysicalAbelianDomain ∧
      hillHminusPhysicalAbelianDomain ⊆ hillHminusCanonicalDirichletDomain ∩ hillHminusCanonicalPsiDomain ∧
      ∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusPhysicalAbelianDomain :=
  ⟨isOpen_hillHminusPhysicalAbelianDomain,isConnected_hillHminusPhysicalAbelianDomain,
    (fun _ hq => ⟨hillHminusPhysicalAbelianDomain_subset_Dirichlet hq,hillHminusPhysicalAbelianDomain_subset_Psi hq⟩),
    fun q => real_mem_hillHminusPhysicalAbelianDomain _ (originalPeriodOneCoefficients_real q)⟩

theorem original_Hill_intrinsic_offIndex_Abelian_analytic :
    ∀ n m : ℕ+, m ≠ n →
      AnalyticOnNhd ℂ (hillHminusPhysicalOffIndexAbelianValue n m) hillHminusPhysicalAbelianDomain ∧
      ∀ q ∈ hillHminusPhysicalAbelianDomain, hillHminusDirichletSheet m q = 0 →
        hillHminusPhysicalOffIndexAbelianValue n m q = 0 :=
  fun n m hmn => ⟨analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn,
    hillHminusPhysicalOffIndexAbelianValue_zero_of_sheet_zero n m hmn⟩

theorem original_Hill_intrinsic_Abelian_value_eq_EVERY_real_patch (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : OriginalHminusOnePotential)
    (hq : originalPeriodOneCoefficients q ∈ P.source) :
    hillHminusPhysicalOffIndexAbelianValue n m (originalPeriodOneCoefficients q) =
      hillHminusDirichletSheet m (originalPeriodOneCoefficients q)*P.offIndexAbelianEnergyQuotient n m
        (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q),originalPeriodOneCoefficients q) := by
  rw [hillHminusPhysicalOffIndexAbelianValue_eq_patch_of_real P n m hmn _ hq (originalPeriodOneCoefficients_real q)]
  exact P.physicalOffIndexAbelianValue_eq_actual_sheet_mul_energy_quotient_of_real n m _ hq
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_physical_Abelian_WHOLE_complex_chart_overlap
    (B C : HillPhysicalAbelianSourceBall) (n m : ℕ+) (hmn : m ≠ n) :
    EqOn (B.value n m) (C.value n m) (B.source ∩ C.source) := B.value_eq_on_overlap C n m hmn

end NLS.Articles.KdVPseudomeasures
