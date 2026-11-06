import NLS.Articles.KdVConvexity.GlobalFrequencyActionDescent
import NLS.Articles.KdVKdV2Frequencies.NativeHilbertWeakActionComparison
import NLS.SequenceSpaces.PositiveOneReindex
import NLS.KdV.HillRoughScalarRealityOn

/-! The global physical action charts use an enumeration of positive labels.
Literal positive sampling transports the SAME native weak actions into that
enumeration; no action or frequency rescaling is introduced. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

def weakActionEnumeration : Coeff 1 →L[ℂ] Coeff 1 := positiveOneReindexPullCLM actionIndexEquiv

@[simp] theorem weakActionEnumeration_apply (a : Coeff 1) (k : ℤ) :
    weakActionEnumeration a k=a (actionIndexEquiv k : ℤ) := rfl

theorem weakActionEnumeration_hilbert (a : ActionSpace) :
    weakActionEnumeration (hilbertWeakActions a)=baseActionNormalization (baseActionInclusion a) := by
  ext k
  rw [weakActionEnumeration_apply,hilbertWeakActions_index]
  change _=(baseActionWeight k : ℂ)*(baseActionInclusion a).val k
  rw [baseActionInclusion_apply]

theorem weakActionEnumeration_nonnegative (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) :
    weakActionEnumeration a∈Coeff.nonnegativeLocus 1 := fun k => ha (actionIndexEquiv k : ℤ)

theorem weakActionEnumeration_native (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val) :
    weakActionEnumeration (D.nativeWeakActionSequence 1 q)=
      baseActionNormalization (baseActionInclusion (originalActionInclusion b.val)) := by
  ext k
  rw [weakActionEnumeration_apply,D.nativeWeakActionSequence_apply 1 3 (by norm_num) q,hb,
    originalPositiveActionInsertion_apply,Equiv.symm_apply_apply,weakActionWeight_positive]
  change _=(baseActionWeight k : ℂ)*(baseActionInclusion (originalActionInclusion b.val)).val k
  rw [baseActionInclusion_apply,originalActionInclusion_apply,Equiv.symm_apply_apply]

theorem physical_pair_actions_at_native (D : GlobalRoughAbelianForwardData)
    (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2)
    (hz : z∈P.domain) (hzr : z∈Coeff.realPairLocus 2)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (hp : P.potential z=nativeHillSource 1 q.val)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q)=originalActionInclusion b.val) :
    baseActionNormalization (baseActionInclusion (originalActionInclusion b.val))=
      quadraticActionsExponent (q := 1) z := by
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hact : baseActionInclusion (originalActionInclusion b.val)=normalizedCoordinateActions z := by
    rw [←hb,baseActionInclusion_physicalHilbertActions I hrec,nativeH1PhysicalRepresentative_rough_source]
    have he := Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec
      (P.potential z) (P.real_potential z hz hzr) z hzr (P.signed_inverse z hz)
    rwa [hp] at he
  rw [hact]
  exact WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z

theorem physicalMiuraFrequencyChart_real (D : GlobalRoughAbelianForwardData)
    (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne)
    (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0) (hq : q∈B.domain) (n : ℕ+) :
    (B.correction n q).im=0 := by
  apply hillRoughScalar_real_of_native_real_on B.domain B.domain_open (B.correction n)
    (B.analytic_correction n).continuousOn ?_ q hqr hqm hq
  intro u hu
  have hs : hillOriginalHminusSource (nativeHillPhysicalSource 1 u.val u.property.1).val=nativeHillSource 1 u.val := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical 1 u.val u.property.1).symm
  have he := native_physical_frequency_eq_miura_chart D B u (by rwa [hs]) n
  rw [hs] at he
  have hc : (2*(n : ℂ)*Real.pi)^3=(((2*(n : ℝ)*Real.pi)^3 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [←he,hc]
  simp only [sub_im,ofReal_im,sub_self]

theorem exists_physical_pair_of_nonnegative_actions (D : GlobalRoughAbelianForwardData)
    (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
    ∃ P : PhysicalFrequencyPairChart D, ∃ z : Coeff 2 × Coeff 2,
      z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧ quadraticActionsExponent (q := 1) z=b := by
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hsurj⟩ := exists_global_analytic_Arnold_map_onto_cone
  have hbp : baseActionNormalization.symm b∈WeightedCoeff.nonnegativeLocus baseActionWeight 1 := by
    apply (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 _).mpr
    change baseActionNormalization (baseActionNormalization.symm b)∈Coeff.nonnegativeLocus 1
    rwa [baseActionNormalization.apply_symm_apply]
  obtain ⟨q,hqr,hqm,hqI⟩ := exists_source_of_nonnegative_Arnold_actions Ω hΩr I hI hrec
    (baseActionNormalization.symm b) hbp
  obtain ⟨P,z,hz,hzr,hzq⟩ := exists_physicalFrequencyPairChart D q hqr hqm
  refine ⟨P,z,hz,hzr,?_⟩
  have he := Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec
    (P.potential z) (P.real_potential z hz hzr) z hzr (P.signed_inverse z hz)
  rw [hzq,hqI] at he
  have hh := congrArg baseActionNormalization he
  rw [baseActionNormalization.apply_symm_apply] at hh
  exact (WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z).symm.trans hh.symm

theorem global_physical_family_native_recovery (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (n : ℕ+) :
    G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
      (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨b,hb,hphys⟩ := exists_original_actions_of_native_source D q
  obtain ⟨P,z,hz,hzr,hpq⟩ := exists_physicalFrequencyPairChart D (nativeHillSource 1 q.val)
    (nativeHillSource_real 1 q.val q.property.1) ((nativeHillSource_apply 1 q.val 0).trans q.property.2)
  rw [weakActionEnumeration_native D q b hb,physical_pair_actions_at_native D P z hz hzr q hpq b hphys,
    hrec P z hz hzr n]
  have hs : hillOriginalHminusSource (nativeHillPhysicalSource 1 q.val q.property.1).val=P.potential z := by
    rw [hillOriginalHminusSource_eq_physical,hpq]
    exact (nativeHillSource_eq_physical 1 q.val q.property.1).symm
  have he := native_physical_frequency_eq_miura_chart D P.source_chart q
    (by rw [hs];exact P.source_mem z hz) n
  rw [hs] at he
  exact he.symm

end NLS.Articles.KdVKdV2Frequencies
