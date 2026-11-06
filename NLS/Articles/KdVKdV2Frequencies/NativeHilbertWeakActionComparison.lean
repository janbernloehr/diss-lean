import NLS.Articles.KdVKdV2Frequencies.OriginalHilbertActionLift
import NLS.Articles.KdVKdV2Frequencies.NativeWeakActionCoordinates
import NLS.Articles.KdVKdV2Frequencies.FiniteGapRoughFirstVariation
import NLS.Articles.KdVKdV2Frequencies.OriginalPhysicalKdVFrequencyComparison

/-! The Hilbert-to-weak inclusion recovers the actual weak actions of the
SAME native map. Conversely the SAME native inverse realizes every original
cubic-weight action, with its actual physical frequency unchanged. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem nativeHilbertWeakActionSequence (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    hilbertWeakActions (originalActionInclusion
      (physicalHilbertActionReindex (D.nativeSourceActionSequence 1 3 (by norm_num) q)))=
        D.nativeWeakActionSequence 1 q := by
  ext j
  rw [D.nativeWeakActionSequence_apply 1 3 (by norm_num) q]
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    let k := actionIndexEquiv.symm n
    have he : (actionIndexEquiv k : ℤ)=j := by
      rw [Equiv.apply_symm_apply]
      exact Int.toNat_of_nonneg hj.le
    rw [←he,hilbertWeakActions_index,originalActionInclusion_apply,
      physicalHilbertActionReindex_coefficient,←weakActionWeight_positive k]
    simp only [Equiv.apply_symm_apply]
  · rw [hilbertWeakActions_nonpositive _ j (by omega),D.nativeSourceActionSequence_apply,
      if_neg hj,mul_zero]

/-- The native representative chosen by the original independent energy has
precisely its intrinsic original frequency, also on the cone boundary. -/
theorem originalActionPotential_native_frequency (D : GlobalRoughAbelianForwardData)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1) (n : ℕ+) :
    let q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) :=
      ⟨D.originalActionPotential 1 3 (by norm_num) a,
        D.originalActionPotential_real 1 3 (by norm_num) a,D.originalActionPotential_zero 1 3 (by norm_num) a⟩
    D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n=D.originalKdVFrequency a n := by
  intro q
  have he : originalPositiveActions 1 3 (by norm_num) (D.rawIntegerForwardHomeomorph 1 q)=a :=
    Subtype.ext (D.originalActionPotential_source_actions a)
  change D.originalKdVFrequency (originalPositiveActions 1 3 (by norm_num) (D.rawIntegerForwardHomeomorph 1 q)) n=_
  rw [he]

/-- Any genuine weak-action factor of the actual native frequency agrees
with the global Hilbert gradient at EVERY original weighted action point.
The subsequent unconditional theorem supplies these factors simultaneously. -/
theorem weakFrequency_eq_gradient_on_original_actions
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (ρ : ℝ) (g : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
      D.nativeWeakActionSequence 1 q∈Metric.ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
        g n (D.nativeWeakActionSequence 1 q)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : hilbertWeakActions (originalActionInclusion b.val)∈Metric.ball (0 : Coeff 1) ρ) (n : ℕ+) :
    g n (hilbertWeakActions (originalActionInclusion b.val))=
      actionGradient E.hamiltonian (originalActionInclusion b.val) n := by
  let a : WeightedCoeff.positiveActionLocus (Weight.sobolev 3) 1 :=
    ⟨originalHilbertActionLift b.val,originalHilbertActionLift_positive b.val b.property⟩
  let q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) :=
    ⟨D.originalActionPotential 1 3 (by norm_num) a,
      D.originalActionPotential_real 1 3 (by norm_num) a,D.originalActionPotential_zero 1 3 (by norm_num) a⟩
  have hact := D.originalActionPotential_source_actions a
  have hw := D.nativeHilbertWeakActionSequence q
  rw [hact,physicalHilbertActionReindex_lift] at hw
  rw [hw] at hb ⊢
  have h := hrec q hb n
  rw [D.originalActionPotential_native_frequency a n] at h
  have hdisp : (2*(n : ℂ)*Real.pi)^3=(((2*Real.pi*(n : ℝ))^3 : ℝ) : ℂ) := by push_cast;ring
  rw [hdisp] at h
  have hg := D.originalKdVFrequency_correction_eq_gradient E a n
  rw [physicalHilbertActionReindex_lift] at hg
  exact h.trans hg

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
