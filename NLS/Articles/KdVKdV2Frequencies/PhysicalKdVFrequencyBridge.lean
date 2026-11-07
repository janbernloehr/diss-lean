import NLS.Articles.KdVConvexity.WeakPhysicalPhaseEvolution
import NLS.Articles.KdVKdV2Frequencies.ActualNativeFlowCompatibility

/-! Exact identification of the retained calibrated weak KdV phase group
with the physical base-action phase group. No frequency, action, time or
source normalization is changed. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

theorem baseActionNormalization_weakPhysicalActions (z : physicalRealDeletedSubmodule) :
    baseActionNormalization (weakPhysicalActions z)=nativeTargetActions z :=
  WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight
    (deletedToSignedPair actionIndexEquiv z.val)

theorem native_zero_frequency_matches_physical
    (B : BasePhysicalFrequencyExtension) (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (z : physicalRealDeletedSubmodule) (n : ℕ+) :
    B.weakPhysicalFrequency z n=nativeTargetKdVFrequency 0 (by norm_num) G z n := by
  have hc : (2*(n:ℂ)*Real.pi)^3=(((2*(n:ℝ)*Real.pi)^3:ℝ):ℂ) := by push_cast;rfl
  simp only [BasePhysicalFrequencyExtension.weakPhysicalFrequency,hB,
    baseActionNormalization_weakPhysicalActions,nativeTargetKdVFrequency,nativeTargetWeakActions,
    show (2:ℝ)*0-1= -1 by norm_num,normalizedSobolevWeakActionInclusion_base,
    hc,Complex.add_re,Complex.ofReal_re]
  exact add_comm _ _

theorem native_zero_signed_frequency_matches_physical
    (B : BasePhysicalFrequencyExtension) (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (z : physicalRealDeletedSubmodule) :
    nativeTargetKdVSignedFrequency 0 (by norm_num) G z=
      signedPositiveFrequency (B.weakPhysicalFrequency z) := by
  have hp (j : ℤ) (hj : 0<j) : nativeTargetKdVSignedFrequency 0 (by norm_num) G z j=
      signedPositiveFrequency (B.weakPhysicalFrequency z) j := by
    let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n:ℤ)=j := by change (j.toNat:ℤ)=j;omega
    rw [←hn,nativeTargetKdVSignedFrequency_positive,signedPositiveFrequency_positive,
      native_zero_frequency_matches_physical B G hB]
  funext j
  rcases lt_trichotomy 0 j with hj|hj|hj
  · exact hp j hj
  · subst j
    simp only [nativeTargetKdVSignedFrequency,signedHamiltonianFrequency_zero,signedPositiveFrequency_zero]
  · have h := hp (-j) (by omega)
    rw [nativeTargetKdVSignedFrequency_odd,signedPositiveFrequency_neg] at h
    exact neg_injective h

theorem native_zero_phase_matches_physical
    (B : BasePhysicalFrequencyExtension) (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (time : ℝ) (z : physicalRealDeletedSubmodule) :
    nativeTargetKdVPhaseFlow 0 (by norm_num) G time z=B.weakPhysicalPhaseFlow time z := by
  apply Subtype.ext
  apply Subtype.ext
  ext j
  change (physicalRealPhaseRotation _ _ time z).val.val j=
    (physicalRealDeletedPhaseFlow _ _ time z).val.val j
  rw [physicalRealPhaseRotation_apply,physicalRealDeletedPhaseFlow_apply,
    native_zero_signed_frequency_matches_physical B G hB]

theorem native_zero_source_flow_matches_physical
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (time : ℝ) (a : physicalRealDeletedSubmodule) :
    nativeKdVSourceFlow D 0 (by norm_num) G time a=D.weakPhysicalPhaseEvolution B time a := by
  have hf (b : physicalRealDeletedSubmodule) : D.realNativeForward 0 (by norm_num) b=D.realWeakHomeomorph b := by
    have h := D.realNativeForward_weak_commuting 0 (by norm_num) b
    simpa only [show (0:ℝ)-1/2= -1/2 by ring,show (0:ℝ)-1= -1 by ring,
      physicalRealSobolevInclusion_self,D.realWeakHomeomorph_apply] using h
  have hi (b : physicalRealDeletedSubmodule) : D.realNativeInverse 0 (by norm_num) b=D.realWeakHomeomorph.symm b := by
    have h := D.realNativeInverse_weak_commuting 0 (by norm_num) b
    simpa only [show (0:ℝ)-1/2= -1/2 by ring,show (0:ℝ)-1= -1 by ring,
      physicalRealSobolevInclusion_self] using h
  rw [nativeKdVSourceFlow,native_zero_phase_matches_physical B G hB,hf,hi]
  rfl

/-- An actual calibrated correction family gives a physical base family
with its exact frequency formula, without expanding its construction in
later native solution proofs. -/
theorem exists_calibrated_base_frequency
    (D : GlobalRoughAbelianForwardData) (V : Set (Coeff 1))
    (G : ℕ+ → Coeff 1 → ℂ) (hV : IsOpen V)
    (hcone : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n,AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    ∃ B : BasePhysicalFrequencyExtension,
      ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3 := by
  refine ⟨basePhysicalFrequencyOfNormalizedFamily V G hV hcone hG
    (physical_frequency_action_factor_recovery D G hrec),?_⟩
  intro n a
  unfold basePhysicalFrequencyOfNormalizedFamily
  generalize_proofs
  rename_i _hscalar hprops _hbounded _htwo
  rcases hprops with ⟨hopen,hpos,ha,hrec⟩
  rfl

end NLS.Articles.KdVKdV2Frequencies
