import NLS.ZakharovShabat.SymmetricSignedGapFiniteBound
import NLS.ZakharovShabat.SourceFiniteGapCompactContainer

/-! # Compact preimages of finite-support signed-gap outputs

The physical finite-gap trace bound controls source norms. The actual
Birkhoff homeomorphism then gives a compact source container, and the
continuous left inverse of the symmetric coordinates transports it back
to the real sequence space. Closed preimages of compact finite-support
output sets are therefore compact in the original Hilbert norm.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Bounded signed-gap outputs with fixed finite support have a compact coordinate container. -/
theorem exists_compact_symmetricSignedGap_container
    (S : Finset ℤ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : Set (RealCoeff 2), IsCompact K ∧
      ∀ a : RealCoeff 2,
      (∀ n ∉ S, symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0) →
      ‖symmetricSourceSignedGapMap (by simp) (by norm_num) a‖ ≤ R → a ∈ K := by
  obtain ⟨K,hK,hcontains⟩ := exists_compact_source_container_of_finite_gap_support
    S (2*(S.card : ℝ)*R) (by positivity)
  let P : realTypeSourceSubmodule 2 → RealCoeff 2 := fun φ => Coeff.reCLM 2 φ.val.snd
  have hP : Continuous P :=
    (Coeff.reCLM 2).continuous.comp ((WithLp.continuous_snd _ _ _).comp continuous_subtype_val)
  refine ⟨P '' K,hK.image hP,?_⟩
  intro a hS hbound
  refine ⟨symmetricRealSourceCoefficients 2 a,?_,re_snd_symmetricSourceCoefficients a⟩
  apply hcontains
  · exact norm_symmetricSource_le_of_finite_signedGap_bound a S R hS hbound
  · intro n hn
    change canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) n = 0
    rw [periodicGap_symmetricSource_eq_abs_signedGap,hS n hn]
    simp

/-- Compact sets of outputs supported in a common finite set have compact full preimages. -/
theorem isCompact_symmetricSignedGap_preimage_of_finite_support
    (S : Finset ℤ) (K : Set (RealCoeff 2)) (hK : IsCompact K)
    (hS : ∀ y ∈ K, ∀ n ∉ S, y n = 0) :
    IsCompact ((symmetricSourceSignedGapMap (by simp) (by norm_num)) ⁻¹' K) := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C,hC,hcontains⟩ := exists_compact_symmetricSignedGap_container S R hR.le
  have hc : Continuous (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) :=
    continuous_iff_continuousAt.mpr fun a =>
      (analyticAt_symmetricSourceSignedGapMap (by simp) (by norm_num) a).continuousAt
  apply hC.of_isClosed_subset (hK.isClosed.preimage hc)
  intro a ha
  exact hcontains a (hS _ ha) (hbound _ ha)

end NLS.ZakharovShabat
