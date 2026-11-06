import NLS.Articles.KdVKdV2Frequencies.GlobalKdVHierarchyActionFactors
import NLS.SequenceSpaces.WeightedPositiveActionDerivatives

/-! # Physical hierarchy Hamiltonians on the original positive action cones

Actions determine a genuine raw real target and hence a physical native
potential via the fixed global inverse. This definition is independent of
any choice of an analytic extension into nonphysical coordinate directions.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

/-- The actual original signed products, as a point of the true positive-index cone. -/
def originalPositiveActions (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1 :=
  ⟨sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z,
    sobolevSignedActionSequence_nonnegative r ((m : ℝ)+1/2) hrs z,by
      intro n hn
      rw [sobolevSignedActionSequence_apply,if_neg (by omega)]⟩

@[simp] theorem originalPositiveActions_val (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2))) :
    (originalPositiveActions m r hrs z).val = sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z := rfl

/-- A genuine real raw native Birkhoff target with the prescribed original actions. -/
def originalActionTarget (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)) :=
  Classical.choose (exists_sobolevSignedActionSequence_preimage r ((m : ℝ)+1/2) hrs
    a.val a.property.1 a.property.2)

theorem originalActionTarget_actions (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) :
    sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs (originalActionTarget m r hrs a) = a.val :=
  Classical.choose_spec (exists_sobolevSignedActionSequence_preimage r ((m : ℝ)+1/2) hrs
    a.val a.property.1 a.property.2)

namespace GlobalRoughAbelianForwardData

/-- The actual real mean-zero physical H^m potential with prescribed actions. -/
def originalActionPotential (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) : ScalarSobolev m :=
  D.rawIntegerInverseSource m (originalActionTarget m r hrs a)

theorem originalActionPotential_real (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2)) (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1)
    (n : ℤ) : (D.originalActionPotential m r hrs a).val (-n) =
      conj ((D.originalActionPotential m r hrs a).val n) :=
  D.rawIntegerInverseSource_real m (originalActionTarget m r hrs a) n

theorem originalActionPotential_zero (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2)) (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) :
    (D.originalActionPotential m r hrs a).val 0 = 0 :=
  D.rawIntegerInverseSource_zero m (originalActionTarget m r hrs a)

/-- The independently defined physical H_m on the original action cone. -/
def originalActionHamiltonian (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2))
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) : ℝ :=
  (nativeHillHierarchyHamiltonian m (D.originalActionPotential m r hrs a)).re

theorem originalActionHamiltonian_complex_value (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2)) (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) :
    (D.originalActionHamiltonian m r hrs a : ℂ) =
      nativeHillHierarchyHamiltonian m (D.originalActionPotential m r hrs a) := by
  apply Complex.ext
  · rfl
  · exact (nativeHillHierarchyHamiltonian_im_eq_zero m _
      (D.originalActionPotential_real m r hrs a) (D.originalActionPotential_zero m r hrs a)).symm

end GlobalRoughAbelianForwardData

/-- A genuine analytic factor of the independent physical hierarchy Hamiltonian.
Every original raw native real target is recovered, including closed gaps. -/
structure OriginalHierarchyActionFactor (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ)
    (hrs : r=2*((m : ℝ)+1/2)) where
  domain : Set (WeightedCoeff (Weight.sobolev r) 1)
  value : WeightedCoeff (Weight.sobolev r) 1 → ℂ
  domain_open : IsOpen domain
  nonnegative_subset_domain : WeightedCoeff.nonnegativeLocus (Weight.sobolev r) 1 ⊆ domain
  analytic : AnalyticOnNhd ℂ value domain
  target_recovery : ∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)),
    value (sobolevSignedActionSequence r ((m : ℝ)+1/2) hrs z) =
      nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z)

/-- These factors exist for the actual original hierarchy, without an abstract
Hamiltonian, spectral-invariance, or analytic-action assumption. -/
theorem nonempty_originalHierarchyActionFactor (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) :
    Nonempty (OriginalHierarchyActionFactor D m r hrs) := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_rawNativeHamiltonian_analytic_action_factor m r hrs
    (nativeHillHierarchyHamiltonian m) (fun q _ => analyticAt_nativeHillHierarchyHamiltonian m q)
    (nativeHillHierarchyHamiltonian_eq_of_discriminant_eq m)
  exact ⟨⟨U,g,hU,hpos,hg,hrec⟩⟩

namespace OriginalHierarchyActionFactor
variable {D : GlobalRoughAbelianForwardData} {m : ℕ} {r : ℝ} {hrs : r=2*((m : ℝ)+1/2)}

/-- The analytic factor recovers the independently defined physical action Hamiltonian. -/
theorem value_eq_physical_actionHamiltonian (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) :
    F.value a.val = (D.originalActionHamiltonian m r hrs a : ℂ) := by
  rw [D.originalActionHamiltonian_complex_value]
  exact (congrArg F.value (originalActionTarget_actions m r hrs a)).symm.trans
    (F.target_recovery (originalActionTarget m r hrs a))

/-- Factor values on every true nonnegative action sequence are real. -/
theorem value_im_eq_zero (F : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) : (F.value a.val).im = 0 := by
  rw [F.value_eq_physical_actionHamiltonian a]
  exact Complex.ofReal_im _

/-- Physical recovery, without fixing an analytic extension, determines every
value on the whole actual cone, including all infinite-support actions. -/
theorem value_eq_on_positive_actions (F G : OriginalHierarchyActionFactor D m r hrs)
    (a : WeightedCoeff.positiveActionLocus (Weight.sobolev r) 1) : F.value a.val = G.value a.val :=
  (F.value_eq_physical_actionHamiltonian a).trans (G.value_eq_physical_actionHamiltonian a).symm

end OriginalHierarchyActionFactor
namespace GlobalRoughAbelianForwardData

/-- The action Hamiltonian is the independent physical H_m at ANY native
real mean-zero source with these actual signed Birkhoff coordinates. -/
theorem originalActionHamiltonian_eq_native_of_signed_eq
    (D : GlobalRoughAbelianForwardData) (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : ScalarSobolev m) (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (hqm : q.val 0=0)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((m : ℝ)+1/2)))
    (h : D.signed (nativeHillSource m q) = WeightedCoeff.sobolevInclusion
      (by have := Nat.cast_nonneg (α := ℝ) m; linarith : (-1/2 : ℝ) ≤ (m : ℝ)+1/2) z.val) :
    (D.originalActionHamiltonian m r hrs (originalPositiveActions m r hrs z) : ℂ) =
      nativeHillHierarchyHamiltonian m q := by
  obtain ⟨F⟩ := nonempty_originalHierarchyActionFactor D m r hrs
  calc
    _ = F.value (originalPositiveActions m r hrs z).val :=
      (F.value_eq_physical_actionHamiltonian _).symm
    _ = nativeHillHierarchyHamiltonian m (D.rawIntegerInverseSource m z) := F.target_recovery z
    _ = nativeHillHierarchyHamiltonian m q := congrArg (nativeHillHierarchyHamiltonian m)
      (D.rawIntegerInverseSource_eq_of_signed_eq m q hq hqm z h)

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
