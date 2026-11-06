import NLS.Articles.KdVConvexity.GlobalFrequencyActionDescent
import NLS.Articles.KdVConvexity.BasePhysicalFrequencyExtension
import NLS.ComplexAnalysis.ScalarFamilyAffineTransport
import NLS.SequenceSpaces.WeightedNonnegativeTransport

/-! # Unconditional construction of the actual base-action frequency family -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity
namespace PhysicalFrequencyPairChart

theorem normalized_actions_at_native {D : GlobalRoughAbelianForwardData} (P : PhysicalFrequencyPairChart D)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ P.domain) (hzr : z ∈ Coeff.realPairLocus 2)
    (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (hp : P.potential z=nativeHillSource 1 p.val)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative p)=originalActionInclusion b.val) :
    baseActionNormalization (baseActionInclusion (originalActionInclusion b.val)) =
      quadraticActionsExponent (q := 1) z := by
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hact : baseActionInclusion (originalActionInclusion b.val)=normalizedCoordinateActions z := by
    rw [←hb,baseActionInclusion_physicalHilbertActions I hrec,nativeH1PhysicalRepresentative_rough_source]
    have he := Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec
      (P.potential z) (P.real_potential z hz hzr) z hzr (P.signed_inverse z hz)
    rwa [hp] at he
  rw [hact]
  exact WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z

theorem correction_at_native {D : GlobalRoughAbelianForwardData} (P : PhysicalFrequencyPairChart D)
    (z : Coeff 2 × Coeff 2) (hz : z ∈ P.domain)
    (p : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (hp : P.potential z=nativeHillSource 1 p.val)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : D.nativeSourceActionSequence 1 3 (by norm_num) p=originalPositiveActionInsertion b.val)
    (n : ℕ+) : P.correction n z=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  have hsource : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val=P.potential z := by
    rw [hillOriginalHminusSource_eq_physical,hp]
    exact (nativeHillSource_eq_physical 1 p.val p.property.1).symm
  have hmem : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val ∈ P.source_chart.domain := by
    rw [hsource]
    exact P.source_mem z hz
  have he := original_physical_frequency_eq_miura_chart D P.source_chart p hmem b hb n
  rw [hsource] at he
  exact he.symm

end PhysicalFrequencyPairChart

theorem physical_frequency_action_factor_recovery (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hG : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z ∈ P.domain → z ∈ Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) (n : ℕ+) :
    G n (baseActionNormalization (baseActionInclusion (originalActionInclusion b.val))) +
      (2*(n : ℂ)*Real.pi)^3=originalPhysicalFrequency b n := by
  let p := nativeOriginalActionSource D b
  let q := nativeHillSource 1 p.val
  have hqr : IsRealPeriodOneHminusOne q := nativeHillSource_real 1 p.val p.property.1
  have hqm : q.val 0=0 := (nativeHillSource_apply 1 p.val 0).trans p.property.2
  obtain ⟨P,z,hz,hzr,hzq⟩ := exists_physicalFrequencyPairChart D q hqr hqm
  rw [P.normalized_actions_at_native z hz hzr p hzq b (nativeOriginalActionSource_physical_actions D b),
    hG P z hz hzr n,P.correction_at_native z hz p hzq b (nativeOriginalActionSource_actions D b) n]
  exact sub_add_cancel _ _

def normalizedBaseFrequency (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (b : BaseActionSpace) : ℂ :=
  G n (baseActionNormalization b)+(2*(n : ℂ)*Real.pi)^3

/-- Transport an actual normalized common family back to the original
weighted base action norm, retaining its physical values. -/
def basePhysicalFrequencyOfNormalizedFamily
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hcone : Coeff.nonnegativeLocus 1 ⊆ V)
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      normalizedBaseFrequency G n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n) :
    BasePhysicalFrequencyExtension := by
  obtain ⟨hopen,hpos,ha,hrec⟩ := NLS.ComplexAnalysis.scalarFamily_add_properties_preimage
    baseActionNormalization (fun n : ℕ+ => (2*(n : ℂ)*Real.pi)^3) G V hV
    (WeightedCoeff.nonnegativeLocus baseActionWeight 1) (Coeff.nonnegativeLocus 1)
    (fun b hb => WeightedCoeff.weightNormalization_nonnegative baseActionWeight 1 b hb) hcone hG
    (∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      normalizedBaseFrequency G n (baseActionInclusion (originalActionInclusion b.val))=originalPhysicalFrequency b n)
    hphysical
  exact ⟨baseActionNormalization ⁻¹' V,normalizedBaseFrequency G,hopen,hpos,ha,hrec⟩

/-- The whole positive base-action cone has one common complex-open
neighborhood carrying every actual physical KdV frequency analytically.
Recovery holds on the ENTIRE original cone, including zero actions and
infinite support. The incompatible printed O(1) bound is omitted. -/
theorem nonempty_basePhysicalFrequencyExtension : Nonempty BasePhysicalFrequencyExtension := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨V,G,hV,hcone,hG,hrecG⟩ := exists_global_physical_frequency_action_corrections D
  exact ⟨basePhysicalFrequencyOfNormalizedFamily V G hV hcone hG
    (physical_frequency_action_factor_recovery D G hrecG)⟩

end NLS.Articles.KdVConvexity
