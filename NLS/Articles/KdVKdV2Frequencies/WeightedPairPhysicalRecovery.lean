import NLS.Articles.KdVKdV2Frequencies.WeightedPairArnoldActions
import NLS.Articles.KdVConvexity.PhysicalFrequencyPairInvariance
import NLS.KdV.HillWeightedPairFiniteSupport

/-! Exact finite physical recovery from normalized Sobolev signed pair identities. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem finite_weighted_pair_physical_recovery
    (D : GlobalRoughAbelianForwardData) (B : PhysicalMiuraFrequencyChart) (t : ℝ)
    (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0)
    (hqB : q∈B.domain) (z : Coeff 2 × Coeff 2) (hzr : z∈Coeff.realPairLocus 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (S : Finset ℤ) (hS : ∀ k : ℤ, k∉S → z.1 k=0 ∧ z.2 k=0) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      (∀ k : ℤ, (Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)*(baseActionInclusion (originalActionInclusion b.val)).val k=
        quadraticActionsExponent (q := 1) z k) ∧
      ∀ n : ℕ+, B.correction n q=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  have hf := positive_finiteSupport_of_weighted_pair_inverse D actionIndexEquiv t q hqr z
    (hi) S hS
  obtain ⟨p,hp⟩ := exists_native_of_finite_positive_support D q hqr hqm hf 1
  obtain ⟨b,hb,hbphys⟩ := exists_original_actions_of_native_source D p
  have hsource : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val=q := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical 1 p.val p.property.1).symm.trans hp
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hact : baseActionInclusion (originalActionInclusion b.val)=I q := by
    rw [←hbphys,baseActionInclusion_physicalHilbertActions I hrec,
      nativeH1PhysicalRepresentative_rough_source,hp]
  refine ⟨b,?_,?_⟩
  · intro k
    rw [hact]
    exact Arnold_action_of_weighted_pair_inverse_identity D Ω hΩr I hI hrec t q hqr z hzr
      (hi) k
  · intro n
    have hmem : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val∈B.domain := by
      rw [hsource]
      exact hqB
    have he := original_physical_frequency_eq_miura_chart D B p hmem b hb n
    rw [hsource] at he
    exact he.symm

end NLS.Articles.KdVKdV2Frequencies
