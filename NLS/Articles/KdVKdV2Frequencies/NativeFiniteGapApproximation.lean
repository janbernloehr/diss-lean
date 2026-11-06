import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapModeOpening
import NLS.Articles.KdVKdV2Frequencies.NativeFrequencyContinuity
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedTruncation

/-! # Genuine finite-gap approximations of every original native real source

The SAME global native inverse acts on literal symmetric signed-target
truncations. Actual spectral gaps close beyond the cutoff, while source,
physical Hill data and intrinsic frequencies converge in their proved norms.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The actual inverse of the finite signed target, in the ORIGINAL native norm. -/
def nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) :=
  (D.rawIntegerForwardHomeomorph m).symm
    (physicalRealMeanZeroWeightedTruncate (Weight.sobolev ((m : ℝ)+1/2)) N
      (D.rawIntegerForwardHomeomorph m q))

/-- Every signed coefficient is the LITERAL truncation of the SAME actual map. -/
theorem nativeFiniteGapApproximation_forward_coefficient (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) (j : ℤ) :
    (D.rawIntegerForwardHomeomorph m (D.nativeFiniteGapApproximation m q N)).val.val j =
      if j∈Finset.Icc (-(N : ℤ)) N then (D.rawIntegerForwardHomeomorph m q).val.val j else 0 := by
  rw [nativeFiniteGapApproximation,(D.rawIntegerForwardHomeomorph m).apply_symm_apply,
    physicalRealMeanZeroWeightedTruncate_coefficient]

/-- The actual ORIGINAL Hill spectral gaps, not just auxiliary target
coordinates, are closed beyond the finite truncation cutoff. -/
theorem nativeFiniteGapApproximation_closed_tail (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ)
    (k : ℕ+) (hk : N<(k : ℕ)) :
    hillRealGapHalfLength (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
      (D.nativeFiniteGapApproximation m q N).property.1).val
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1).property.1
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1).property.2 k=0 := by
  apply (D.rawIntegerForwardHomeomorph_zero_iff_closed m _ k).mp
  rw [nativeFiniteGapApproximation,(D.rawIntegerForwardHomeomorph m).apply_symm_apply]
  exact physicalRealMeanZeroWeightedTruncate_positive_tail _ N _ k hk

/-- Each approximating source satisfies the actual spectral finite-gap
condition used by the physical Hamiltonian frequency identities. -/
theorem nativeFiniteGapApproximation_finite_gap (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (N : ℕ) :
    ∃ S : Finset ℕ+, ∀ k : ℕ+, k∉S → hillRealGapHalfLength
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1).val
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1).property.1
      (nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
        (D.nativeFiniteGapApproximation m q N).property.1).property.2 k=0 := by
  classical
  refine ⟨(Finset.range N).image (fun j => (⟨j+1,by omega⟩ : ℕ+)),?_⟩
  intro k hk
  apply D.nativeFiniteGapApproximation_closed_tail m q N k
  by_contra hh
  have hkN : (k : ℕ)≤N := le_of_not_gt hh
  apply hk
  apply Finset.mem_image.mpr
  refine ⟨(k : ℕ)-1,Finset.mem_range.mpr (by have := k.pos; omega),?_⟩
  apply Subtype.ext
  change (k : ℕ)-1+1=(k : ℕ)
  have := k.pos
  omega

/-- Native source convergence is in the entire inherited original H^m norm. -/
theorem tendsto_nativeFiniteGapApproximation (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    Tendsto (D.nativeFiniteGapApproximation m q) atTop (𝓝 q) := by
  have h := (D.rawIntegerForwardHomeomorph m).symm.continuous.continuousAt.tendsto.comp
    (tendsto_physicalRealMeanZeroWeightedTruncate (Weight.sobolev ((m : ℝ)+1/2))
      (D.rawIntegerForwardHomeomorph m q))
  simpa only [(D.rawIntegerForwardHomeomorph m).symm_apply_apply] using! h

/-- Actual physical Hill sources converge in the original physical L2 topology. -/
theorem tendsto_nativeFiniteGapApproximation_physical (D : GlobalRoughAbelianForwardData) (m : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) :
    Tendsto (fun N => nativeHillPhysicalSource m (D.nativeFiniteGapApproximation m q N).val
      (D.nativeFiniteGapApproximation m q N).property.1) atTop
      (𝓝 (nativeHillPhysicalSource m q.val q.property.1)) :=
  (continuous_nativeHillPhysicalSource m).continuousAt.tendsto.comp (D.tendsto_nativeFiniteGapApproximation m q)

/-- The ACTUAL intrinsic physical frequency converges, also at closed own
modes and infinite-support original sources. -/
theorem tendsto_nativeFiniteGapApproximation_frequency (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (n : ℕ+) :
    Tendsto (fun N => D.nativeSourceHierarchyFrequency m r hrs (D.nativeFiniteGapApproximation m q N) n)
      atTop (𝓝 (D.nativeSourceHierarchyFrequency m r hrs q n)) :=
  (D.continuous_nativeSourceHierarchyFrequency m r hrs n).continuousAt.tendsto.comp
    (D.tendsto_nativeFiniteGapApproximation m q)

/-- Genuine spectral finite-gap sources are dense in EVERY original native
real mean-zero H^m space, with the SAME actual spectral interpretation. -/
theorem dense_native_spectral_finiteGap (D : GlobalRoughAbelianForwardData) (m : ℕ) :
    Dense {q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ)) |
      ∃ S : Finset ℕ+, ∀ k : ℕ+, k∉S → hillRealGapHalfLength
        (nativeHillPhysicalSource m q.val q.property.1).val
        (nativeHillPhysicalSource m q.val q.property.1).property.1
        (nativeHillPhysicalSource m q.val q.property.1).property.2 k=0} := by
  intro q
  exact mem_closure_of_tendsto (D.tendsto_nativeFiniteGapApproximation m q)
    (Eventually.of_forall (D.nativeFiniteGapApproximation_finite_gap m q))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
