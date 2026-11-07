import NLS.Articles.KdVKdV2Frequencies.WeightedPairPhysicalRecovery
import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapHamiltonianVariation
import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevRenormalizedFrequency
import NLS.KdV.PhysicalSharpDiagonalCancellation

/-! Finite physical calibration of the FULL corrected frequency in
the original Sobolev actions, on the SAME actual physical chart. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem finite_weighted_pair_renormalized_recovery
    (D : GlobalRoughAbelianForwardData) (B : PhysicalMiuraFrequencyChart) (t : ℝ)
    (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0)
    (hqB : q∈B.domain) (z : Coeff 2 × Coeff 2) (hzr : z∈Coeff.realPairLocus 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (S : Finset ℤ) (hS : ∀ k : ℤ, k∉S → z.1 k=0 ∧ z.2 k=0) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      (∀ k : ℤ, (Weight.sobolev (2*t-1) (actionIndexEquiv k : ℤ) : ℂ)*
        (baseActionInclusion (originalActionInclusion b.val)).val k=quadraticActionsExponent (q := 1) z k) ∧
      ∀ n : ℕ+, B.correction n q+12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
        (hillMiuraDiagonal (B.psi.miura.lift q))=
          originalPhysicalFrequency b n-(2*(n:ℂ)*Real.pi)^3+6*b.val.val (actionIndexEquiv.symm n) := by
  have hf := positive_finiteSupport_of_weighted_pair_inverse D actionIndexEquiv t q hqr z hi S hS
  obtain ⟨p,hp⟩ := exists_native_of_finite_positive_support D q hqr hqm hf 1
  obtain ⟨b,hb,hbphys⟩ := exists_original_actions_of_native_source D p
  have hsource : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val=q := by
    rw [hillOriginalHminusSource_eq_physical]
    exact (nativeHillSource_eq_physical 1 p.val p.property.1).symm.trans hp
  obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hzero,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hact : baseActionInclusion (originalActionInclusion b.val)=I q := by
    rw [← hbphys,baseActionInclusion_physicalHilbertActions I hrec,
      nativeH1PhysicalRepresentative_rough_source,hp]
  refine ⟨b,?_,?_⟩
  · intro k
    rw [hact]
    exact Arnold_action_of_weighted_pair_inverse_identity D Ω hΩr I hI hrec t q hqr z hzr hi k
  · intro n
    have hmem : hillOriginalHminusSource (nativeHillPhysicalSource 1 p.val p.property.1).val∈B.domain := by
      rw [hsource]
      exact hqB
    have he := original_physical_frequency_eq_miura_chart D B p hmem b hb n
    rw [hsource] at he
    have ha := congrArg (fun a : WeightedCoeff (Weight.sobolev 3) 1 => a.val (n:ℤ)) hb
    rw [D.nativeSourceActionSequence_eq_gap_integral,originalPositiveActionInsertion_apply] at ha
    have hcounter := B.original_counterterm_eq_raw_action (nativeHillPhysicalSource 1 p.val p.property.1) hmem n
    rw [hsource] at hcounter
    rw [← hcounter,ha,← he]

theorem finite_weighted_pair_global_renormalized_calibration
    (D : GlobalRoughAbelianForwardData) (B : PhysicalMiuraFrequencyChart)
    (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q) (hqm : q.val 0=0)
    (hqB : q∈B.domain) (z : Coeff 2 × Coeff 2) (hzr : z∈Coeff.realPairLocus 2)
    (hi : ∀ j : ℤ, (D.signed q).val j=(signedPairToDeleted actionIndexEquiv z).val j/(Weight.sobolev (t-1/2) j : ℂ))
    (S : Finset ℤ) (hS : ∀ k : ℤ, k∉S → z.1 k=0 ∧ z.2 k=0) (n : ℕ+) :
    normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G n (quadraticActionsExponent (q := 1) z)=
      B.correction n q+12*sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
        (hillMiuraDiagonal (B.psi.miura.lift q)) := by
  obtain ⟨b,hb,hf⟩ := finite_weighted_pair_renormalized_recovery D B t q hqr hqm hqB z hzr hi S hS
  have hκ : normalizedSobolevWeakActionInclusion (2*t-1) (by linarith) (quadraticActionsExponent (q := 1) z)=
      baseActionNormalization (baseActionInclusion (originalActionInclusion b.val)) := by
    ext k
    rw [normalizedSobolevWeakActionInclusion_apply,← hb k,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    rfl
  have ha : quadraticActionsExponent (q := 1) z (actionIndexEquiv.symm n)/(Weight.sobolev (2*t-1) (n:ℤ) : ℂ)=
      b.val.val (actionIndexEquiv.symm n) := by
    have h := hb (actionIndexEquiv.symm n)
    simp only [Equiv.apply_symm_apply,baseActionInclusion_apply,originalActionInclusion_apply] at h
    rw [← h,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
  rw [normalizedSobolevRenormalizedFrequency,hκ,ha,weak_scalar_original_physical_recovery D G hrec b n]
  exact (hf n).symm

end NLS.Articles.KdVKdV2Frequencies
