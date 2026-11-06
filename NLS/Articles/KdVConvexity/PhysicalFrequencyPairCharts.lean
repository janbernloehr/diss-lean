import NLS.Articles.KdVConvexity.PhysicalMiuraFrequencyRecovery
import NLS.Articles.KdVConvexity.LocalSpectralPairCharts
import NLS.KdV.HillRoughFinitePairRegularity

/-! # Actual common local pair charts for all physical frequency corrections -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

structure PhysicalFrequencyPairChart (D : GlobalRoughAbelianForwardData) where
  domain : Set (Coeff 2 × Coeff 2)
  domain_open : IsOpen domain
  potential : (Coeff 2 × Coeff 2) → PeriodOneHminusOne
  analytic_potential : AnalyticOnNhd ℂ potential domain
  mean_zero : ∀ z ∈ domain, (potential z).val 0=0
  signed_inverse : ∀ z ∈ domain,
    D.signed (potential z) = WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2))
      (signedPairToDeleted actionIndexEquiv z)
  real_potential : ∀ z ∈ domain, z ∈ Coeff.realPairLocus 2 → IsRealPeriodOneHminusOne (potential z)
  source_chart : PhysicalMiuraFrequencyChart
  source_mem : ∀ z ∈ domain, potential z ∈ source_chart.domain

namespace PhysicalFrequencyPairChart

def correction {D : GlobalRoughAbelianForwardData} (P : PhysicalFrequencyPairChart D)
    (n : ℕ+) (z : Coeff 2 × Coeff 2) : ℂ := P.source_chart.correction n (P.potential z)

theorem analytic_correction {D : GlobalRoughAbelianForwardData} (P : PhysicalFrequencyPairChart D) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.correction n) P.domain := by
  intro z hz
  exact (P.source_chart.analytic_correction n _ (P.source_mem z hz)).comp (P.analytic_potential z hz)

/-- Every finite real target recovers the actual physical frequency in
its original actions. The native source is a proved conclusion. -/
theorem finite_physical_recovery {D : GlobalRoughAbelianForwardData} (P : PhysicalFrequencyPairChart D)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ P.domain) (hr : z ∈ Coeff.realPairLocus 2)
    (S : Finset ℤ) (hS : ∀ k : ℤ, k ∉ S → z.1 k=0 ∧ z.2 k=0) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      baseActionInclusion (originalActionInclusion b.val)=normalizedCoordinateActions z ∧
      ∀ n : ℕ+, P.correction n z=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  have hqr := P.real_potential z hz hr
  have hf := positive_finiteSupport_of_pair_inverse D actionIndexEquiv (P.potential z) hqr z
    (P.signed_inverse z hz) S hS
  obtain ⟨p,hp⟩ := exists_native_of_finite_positive_support D (P.potential z) hqr (P.mean_zero z hz) hf 1
  obtain ⟨b,hb,hbphys⟩ := exists_original_actions_of_native_source D p
  have hsource : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val=P.potential z := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical 1 p.val p.property.1).symm.trans hp
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hactions : baseActionInclusion (originalActionInclusion b.val)=normalizedCoordinateActions z := by
    rw [←hbphys,baseActionInclusion_physicalHilbertActions I hrec,
      nativeH1PhysicalRepresentative_rough_source,hp]
    exact Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec (P.potential z) hqr z hr (P.signed_inverse z hz)
  refine ⟨b,hactions,?_⟩
  intro n
  have hmem : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val ∈ P.source_chart.domain := by
    rw [hsource]
    exact P.source_mem z hz
  have he := original_physical_frequency_eq_miura_chart D P.source_chart p hmem b hb n
  rw [hsource] at he
  exact he.symm

end PhysicalFrequencyPairChart

/-- One pair domain precedes all frequency indices at every actual real
rough mean-zero source, retaining the original signed inverse identity. -/
theorem exists_physicalFrequencyPairChart (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0=0) :
    ∃ P : PhysicalFrequencyPairChart D, ∃ z : Coeff 2 × Coeff 2,
      z ∈ P.domain ∧ z ∈ Coeff.realPairLocus 2 ∧ P.potential z=q := by
  obtain ⟨z,hzr,U,hU,hzU,Q,hQ,hQz,hd⟩ := exists_hillRough_pair_inverse D actionIndexEquiv q hr hm
  obtain ⟨B,hqB,_⟩ := exists_physicalMiuraFrequencyChart q hr 0
  let V := U ∩ Q ⁻¹' B.domain
  refine ⟨⟨V,hQ.continuousOn.isOpen_inter_preimage hU B.domain_open,Q,hQ.mono inter_subset_left,
    (fun w hw => (hd w hw.1).1),(fun w hw => (hd w hw.1).2.1),
    (fun w hw hwr => (hd w hw.1).2.2 hwr),B,(fun w hw => hw.2)⟩,z,⟨hzU,?_⟩,hzr,hQz⟩
  change Q z ∈ B.domain
  rwa [hQz]

end NLS.Articles.KdVConvexity
