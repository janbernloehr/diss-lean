import NLS.Articles.KdVPseudomeasures.OriginalHillLocalAbelianIntegrals
import NLS.KdV.HillOffIndexAbelianEndpointIntegrals
import NLS.KdV.HillAbelianPhysicalEnergyPullback

/-! Actual off-index Abelian endpoint normalization on original
complex gap discs, including ALL collapsed gaps. The primitive is
also the genuine improper polygonal endpoint integral. The energy
pullback and endpoint labels retain their physical normalization. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_common_offIndex_Abelian_endpoint_normalization
    (P : HillProductEquationPatch) (q₀ : OriginalHminusOnePotential)
    (hq₀ : originalPeriodOneCoefficients q₀ ∈ P.source) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ originalPeriodOneCoefficients q₀ ∈ V ∧ V ⊆ P.source ∧
      ∀ q ∈ V, ∀ n m : ℕ+, m ≠ n → ∃ F : ℂ → ℂ,
        (∀ z ∈ P.abelianGapDisc m q, HasDerivAt F (P.abelianFrequencyDifferential n (z,q)) z) ∧
        Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicLeft (by norm_num) (by norm_num)
          (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) ∧
        Tendsto F (𝓝[P.abelianGapDisc m q] (canonicalPeriodicRight (by norm_num) (by norm_num)
          (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ))) (𝓝 0) ∧
        ∀ ν ∈ P.abelianGapDisc m q, P.offIndexAbelianEndpointIntegral n m q ν = F ν := by
  obtain ⟨V,hV,hqV,hsub,hF⟩ := P.exists_common_ALL_gap_offIndex_abelian_endpoint_normalization
    _ hq₀ (originalPeriodOneCoefficients_real q₀)
  refine ⟨V,hV,hqV,hsub,?_⟩
  intro q hq n m hmn
  obtain ⟨F,hderiv,hleft,hright⟩ := hF q hq n m hmn
  exact ⟨F,hderiv,hleft,hright,fun ν hν =>
    P.offIndexAbelianEndpointIntegral_eq_normalized_primitive n m q (hsub hq) F hderiv hleft ν hν⟩

theorem original_Hill_Abelian_physical_energy_pullback (P : HillProductEquationPatch)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source)
    (z : ℂ) (hz : 0 < z.re)
    (hroot : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi (originalPeriodOneCoefficients q))) :
    (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),originalPeriodOneCoefficients q) ∈ hillHminusCanonicalEnergyRootDomain ∧
      ∀ n : ℕ+, P.abelianFrequencyDifferential n (z,originalPeriodOneCoefficients q) =
        2*z*hillHminusCanonicalEnergyDifferential n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),originalPeriodOneCoefficients q) :=
  P.abelianFrequencyDifferential_physical_energy_pullback _ hq (originalPeriodOneCoefficients_real q) z hz hroot

theorem original_Hill_Abelian_endpoint_energies (P : HillProductEquationPatch) (m : ℕ+)
    (q : OriginalHminusOnePotential) (hq : originalPeriodOneCoefficients q ∈ P.source) :
    (canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi (originalPeriodOneCoefficients q))) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2-
        (P.parent.parent.miuraBall.actionBall.shift:ℂ) = (hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) (2*(m:ℕ)-1):ℂ) ∧
      (canonicalPeriodicRight (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi (originalPeriodOneCoefficients q))) (periodOnePotential_mem _) ((m:ℕ):ℤ))^2-
        (P.parent.parent.miuraBall.actionBall.shift:ℂ) = (hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) (2*(m:ℕ)):ℂ) :=
  P.abelian_gap_endpoint_energies_eq_original_labels m _ hq (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
