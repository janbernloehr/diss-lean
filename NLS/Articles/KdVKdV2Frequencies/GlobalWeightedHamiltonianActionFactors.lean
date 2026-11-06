import NLS.Articles.KdVKdV2Frequencies.GlobalNativeHamiltonianActionDescent
import NLS.SequenceSpaces.SobolevSignedActionSequence

/-! # Analytic factors of the printed Hamiltonians in the ORIGINAL action norms

H1 has an analytic factor on an open complex neighborhood of the entire
nonnegative weighted l1 cone of order three; H2 has the corresponding
factor of order five. Recovery holds on the entire original raw real
mean-zero h^(3/2) and h^(5/2) domains, with I_n=z_n*z_(-n) exactly.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies

/-- Original H1 actions in weighted l1 of order three. -/
def kdvNativeActionSequence
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) :
    WeightedCoeff (Weight.sobolev 3) 1 :=
  sobolevSignedActionSequence 3 (((1 : ℕ) : ℝ)+1/2) (by norm_num) z

/-- Original H2 actions in weighted l1 of order five. -/
def kdv2NativeActionSequence
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) :
    WeightedCoeff (Weight.sobolev 5) 1 :=
  sobolevSignedActionSequence 5 (((2 : ℕ) : ℝ)+1/2) (by norm_num) z

theorem kdvNativeActionSequence_apply
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) (n : ℤ) :
    (kdvNativeActionSequence z).val n = if 0<n then z.val.val n*z.val.val (-n) else 0 :=
  sobolevSignedActionSequence_apply _ _ _ z n

theorem kdv2NativeActionSequence_apply
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) (n : ℤ) :
    (kdv2NativeActionSequence z).val n = if 0<n then z.val.val n*z.val.val (-n) else 0 :=
  sobolevSignedActionSequence_apply _ _ _ z n

namespace GlobalRoughAbelianForwardData

/-- Exact action normalization in the already fixed raw target chart. -/
theorem nativeActionSequence_normalization (s : ℕ) (r : ℝ) (hrs : r=2*((s : ℝ)+1/2))
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2))) :
    WeightedCoeff.weightIsometry (Weight.sobolev r) 1
      (sobolevSignedActionSequence r ((s : ℝ)+1/2) hrs z) =
      quadraticActionsExponent (q := 1) (Coeff.signedToCartesian (integerTargetNormalization s z).val) := by
  exact sobolevSignedActionSequence_normalized r ((s : ℝ)+1/2) hrs z

/-- Analytic action descent in the literal ORIGINAL weighted action norm,
for any entire native physical spectral invariant. -/
theorem exists_rawNativeHamiltonian_analytic_action_factor
    (D : GlobalRoughAbelianForwardData) (s : ℕ) (r : ℝ) (hrs : r=2*((s : ℝ)+1/2))
    (H : ScalarSobolev s → ℂ) (hH : AnalyticOnNhd ℂ H univ)
    (hiso : ∀ u v : ScalarSobolev s,
      (∀ n : ℤ, u.val (-n) = conj (u.val n)) → (∀ n : ℤ, v.val (-n) = conj (v.val n)) →
      u.val 0 = 0 → v.val 0 = 0 →
      hillHminusDiscriminant (nativeHillSource s u) = hillHminusDiscriminant (nativeHillSource s v) → H u = H v) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev r) 1),
      ∃ g : WeightedCoeff (Weight.sobolev r) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev r) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      ∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((s : ℝ)+1/2)),
        g (sobolevSignedActionSequence r ((s : ℝ)+1/2) hrs z) =
          H (D.rawIntegerInverseSource s z) := by
  obtain ⟨V,g,hV,hpos,hg,hrec⟩ := D.exists_nativeHamiltonian_analytic_action_factor s H hH hiso
  obtain ⟨U,G,hU,hUp,hG,hmatch⟩ := WeightedCoeff.exists_analytic_action_factor_transport
    (Weight.sobolev r) V g hV hpos hg
  refine ⟨U,G,hU,hUp,hG,?_⟩
  intro z
  exact (hmatch _).trans ((congrArg g (nativeActionSequence_normalization s r hrs z)).trans
    (hrec (integerTargetNormalization s z)))

/-- The H1 clause of Theorem 1.1(iii): the ORIGINAL physical Hamiltonian
composed with the SAME global inverse is an analytic function of the
ORIGINAL actions alone on ALL raw h^(3/2), including every closed gap. -/
theorem exists_originalKdV_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 3) 1),
      ∃ g : WeightedCoeff (Weight.sobolev 3) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev 3) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      ∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)),
        g (kdvNativeActionSequence z) = (D.birkhoffKdVHamiltonian z : ℂ) := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_rawNativeHamiltonian_analytic_action_factor 1 3
    (by norm_num) nativeKdVHamiltonian (fun q _ => analyticAt_nativeKdVHamiltonian q)
    nativeKdVHamiltonian_eq_of_discriminant_eq
  refine ⟨U,g,hU,hpos,hg,?_⟩
  intro z
  exact (hrec z).trans (D.birkhoffKdVHamiltonian_complex_value z).symm

/-- The H2 clause of Theorem 1.1(iii), in the ORIGINAL weighted l1 action
space of order five and on the ENTIRE original raw h^(5/2) target. -/
theorem exists_originalKdV2_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 5) 1),
      ∃ g : WeightedCoeff (Weight.sobolev 5) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev 5) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      ∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)),
        g (kdv2NativeActionSequence z) = (D.birkhoffKdV2Hamiltonian z : ℂ) := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_rawNativeHamiltonian_analytic_action_factor 2 5
    (by norm_num) nativeKdV2Hamiltonian (fun q _ => analyticAt_nativeKdV2Hamiltonian q)
    nativeKdV2Hamiltonian_eq_of_discriminant_eq
  refine ⟨U,g,hU,hpos,hg,?_⟩
  intro z
  exact (hrec z).trans (D.birkhoffKdV2Hamiltonian_complex_value z).symm

/-- The original H1 action factor is real on EVERY true nonnegative
positive-index action sequence, in the exact weighted l1 norm of order three. -/
theorem exists_originalKdV_real_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 3) 1),
      ∃ g : WeightedCoeff (Weight.sobolev 3) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev 3) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)),
        g (kdvNativeActionSequence z) = (D.birkhoffKdVHamiltonian z : ℂ)) ∧
      ∀ I : WeightedCoeff (Weight.sobolev 3) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev 3) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_originalKdV_analytic_action_factor
  refine ⟨U,g,hU,hpos,hg,hrec,?_⟩
  intro I hI hzero
  obtain ⟨z,hz⟩ := exists_sobolevSignedActionSequence_preimage 3 (((1 : ℕ) : ℝ)+1/2)
    (by norm_num) I hI hzero
  have he := hrec z
  change kdvNativeActionSequence z = I at hz
  rw [hz] at he
  rw [he]
  exact Complex.ofReal_im _

/-- The original H2 action factor has the same full-cone reality property,
in the exact original weighted l1 norm of order five. -/
theorem exists_originalKdV2_real_analytic_action_factor (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 5) 1),
      ∃ g : WeightedCoeff (Weight.sobolev 5) 1 → ℂ,
      IsOpen U ∧ WeightedCoeff.nonnegativeLocus (Weight.sobolev 5) 1 ⊆ U ∧
      AnalyticOnNhd ℂ g U ∧
      (∀ z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)),
        g (kdv2NativeActionSequence z) = (D.birkhoffKdV2Hamiltonian z : ℂ)) ∧
      ∀ I : WeightedCoeff (Weight.sobolev 5) 1,
        I ∈ WeightedCoeff.nonnegativeLocus (Weight.sobolev 5) 1 →
        (∀ n : ℤ, n ≤ 0 → I.val n = 0) → (g I).im = 0 := by
  obtain ⟨U,g,hU,hpos,hg,hrec⟩ := D.exists_originalKdV2_analytic_action_factor
  refine ⟨U,g,hU,hpos,hg,hrec,?_⟩
  intro I hI hzero
  obtain ⟨z,hz⟩ := exists_sobolevSignedActionSequence_preimage 5 (((2 : ℕ) : ℝ)+1/2)
    (by norm_num) I hI hzero
  have he := hrec z
  change kdv2NativeActionSequence z = I at hz
  rw [hz] at he
  rw [he]
  exact Complex.ofReal_im _

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
