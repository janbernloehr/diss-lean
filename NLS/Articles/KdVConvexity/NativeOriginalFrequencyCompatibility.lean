import NLS.Articles.KdVConvexity.OriginalPositiveActionInsertion
import NLS.Articles.KdVConvexity.NativeH1PhysicalCompatibility
import NLS.Articles.KdVConvexity.IntrinsicPhysicalFrequencies
import NLS.Articles.KdVKdV2Frequencies.FiniteGapRoughFirstVariation

/-! # Equality of the two independently physical frequency definitions

The native hierarchy factor pulls back along literal positive insertion
to the article's full physical action energy. Analytic uniqueness on the
whole nonnegative original cone identifies its cotangent, and therefore
every unscaled action frequency, including every zero action.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
open scoped ComplexConjugate
namespace NLS.Articles.KdVConvexity

def nativeOriginalPositiveActions (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1 :=
  ⟨originalPositiveActionInsertion b.val,originalPositiveActionInsertion_nonnegative b.val b.property,
    originalPositiveActionInsertion_nonpositive b.val⟩

def nativeOriginalActionSource (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)) :=
  ⟨D.originalActionPotential 1 3 (by norm_num) (nativeOriginalPositiveActions b),
    D.originalActionPotential_real 1 3 (by norm_num) (nativeOriginalPositiveActions b),
    D.originalActionPotential_zero 1 3 (by norm_num) (nativeOriginalPositiveActions b)⟩

theorem nativeOriginalActionSource_actions (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    D.nativeSourceActionSequence 1 3 (by norm_num) (nativeOriginalActionSource D b) =
      originalPositiveActionInsertion b.val := by
  let z := originalActionTarget 1 3 (by norm_num) (nativeOriginalPositiveActions b)
  have hz : D.rawIntegerForwardHomeomorph 1 (nativeOriginalActionSource D b)=z := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    have hf := congrArg (fun a : WeightedCoeff (Weight.sobolev (-1/2)) 2 => a.val j)
      (D.rawIntegerForwardHomeomorph_signed 1 (nativeOriginalActionSource D b))
    have hi := congrArg (fun a : WeightedCoeff (Weight.sobolev (-1/2)) 2 => a.val j)
      (D.rawIntegerInverseSource_signed 1 z)
    simp only [WeightedCoeff.sobolevInclusion_apply] at hf hi
    exact hf.trans hi
  change sobolevSignedActionSequence 3 (((1:ℕ):ℝ)+1/2) _
    (D.rawIntegerForwardHomeomorph 1 (nativeOriginalActionSource D b)) = _
  rw [hz]
  exact originalActionTarget_actions 1 3 (by norm_num) (nativeOriginalPositiveActions b)

theorem nativeOriginalActionSource_physical_actions (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    physicalHilbertActions hillH1SpectralWeight
      (nativeH1PhysicalRepresentative (nativeOriginalActionSource D b)) = originalActionInclusion b.val := by
  ext n
  rw [←nativeH1PhysicalRepresentative_actions D (nativeOriginalActionSource D b) n,
    nativeOriginalActionSource_actions,originalPositiveActionInsertion_apply,originalActionInclusion_apply]

/-- Any genuine hierarchy action factor recovers this article's
independently defined physical energy on the ENTIRE original cone. -/
theorem nativeActionFactor_eq_originalPhysicalEnergy (D : GlobalRoughAbelianForwardData)
    (F : OriginalHierarchyActionFactor D 1 3 (by norm_num))
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    F.value (originalPositiveActionInsertion b.val)=originalPhysicalActionEnergy b := by
  have hrec : F.value (originalPositiveActionInsertion b.val) =
      nativeKdVHamiltonian (nativeOriginalActionSource D b).val := by
    have ht := originalActionTarget_actions 1 3 (by norm_num) (nativeOriginalPositiveActions b)
    have hf := F.target_recovery (originalActionTarget 1 3 (by norm_num) (nativeOriginalPositiveActions b))
    rw [nativeHillHierarchyHamiltonian_one] at hf
    exact (congrArg F.value ht).symm.trans hf
  have hp := physicalActionHamiltonian_eq_source
    (⟨originalActionInclusion b.val,originalActionInclusion_mem_domain b.val b.property⟩)
    (nativeH1PhysicalRepresentative (nativeOriginalActionSource D b))
    (nativeH1PhysicalRepresentative_mean_zero _) (nativeOriginalActionSource_physical_actions D b)
  change originalPhysicalActionEnergy b = _ at hp
  exact hrec.trans ((nativeH1PhysicalRepresentative_energy _).symm.trans hp.symm)

/-- The original raw positive coordinate derivative is exactly the
intrinsic physical hierarchy frequency, at all boundary points too. -/
theorem originalPhysicalFrequency_eq_nativeOriginalFrequency (D : GlobalRoughAbelianForwardData)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) (n : ℕ+) :
    originalPhysicalFrequency b n = (D.originalKdVFrequency (nativeOriginalPositiveActions b) n:ℂ) := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D 1 3 (by norm_num)
  have hF := F.analytic _ (F.nonnegative_subset_domain
    (nativeOriginalPositiveActions b).property.1)
  have hG : AnalyticAt ℂ (fun a : OriginalActionSpace => F.value (originalPositiveActionInsertion a)) b.val :=
    hF.comp (f := originalPositiveActionInsertion) (originalPositiveActionInsertion.analyticAt b.val)
  have hrec : (fun c : WeightedCoeff.nonnegativeLocus originalActionWeight 1 =>
      F.value (originalPositiveActionInsertion c.val)) =ᶠ[𝓝 b] originalPhysicalActionEnergy :=
    Eventually.of_forall (nativeActionFactor_eq_originalPhysicalEnergy D F)
  rw [originalPhysicalFrequency,originalPhysicalEnergyDifferential_eq_local_germ b _ hG hrec]
  have hd := hF.differentiableAt.hasFDerivAt.comp b.val originalPositiveActionInsertion.hasFDerivAt
  change (fderiv ℂ (F.value ∘ originalPositiveActionInsertion) b.val) _ = _
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,originalPositiveActionInsertion_single]
  exact (D.originalHierarchyFrequency_eq_factor_derivative 1 3 (by norm_num) F
    (nativeOriginalPositiveActions b) n).symm

theorem nativeSourceFrequency_eq_originalPhysicalFrequency (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (ha : D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val) (n : ℕ+) :
    (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)=originalPhysicalFrequency b n := by
  have he : originalPositiveActions 1 3 (by norm_num) (D.rawIntegerForwardHomeomorph 1 q) =
      nativeOriginalPositiveActions b := Subtype.ext ha
  change (D.originalHierarchyFrequency 1 3 (by norm_num) _ n:ℂ)=_
  rw [he]
  exact (originalPhysicalFrequency_eq_nativeOriginalFrequency D b n).symm

/-- Every actual native H1 source has the article's original weighted
action representative, with both raw action conventions recovered. -/
theorem exists_original_actions_of_native_source (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    ∃ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1,
      D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val ∧
      physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q)=originalActionInclusion b.val := by
  obtain ⟨b,hb,he⟩ := original_domain_has_weighted_representative
    (physicalHilbertActions hillH1SpectralWeight (nativeH1PhysicalRepresentative q))
    (physicalHilbertActions_H1_mem_original_domain (nativeH1PhysicalRepresentative q))
  refine ⟨⟨b,hb⟩,?_,he.symm⟩
  apply Subtype.ext
  funext j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n:ℤ)=j := Int.toNat_of_nonneg hj.le
    rw [←hn,nativeH1PhysicalRepresentative_actions D q n,originalPositiveActionInsertion_apply,
      ←originalActionInclusion_apply,he]
  · rw [D.nativeSourceActionSequence_apply,if_neg hj,
      originalPositiveActionInsertion_nonpositive b j (by omega)]

end NLS.Articles.KdVConvexity
