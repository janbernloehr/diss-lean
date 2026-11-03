import NLS.MKdV.MiuraEncodedActionFactorBalls
import NLS.MKdV.MiuraFiniteEncodedActionRealization
import NLS.SequenceSpaces.FiniteNonnegativeActionAgreement
import NLS.SequenceSpaces.NonnegativeActionGluing

/-! # One global holomorphic forward physical-action/signed-mean factor

Encoded local factors agree on finite nonnegative data by actual H1
realization and global representative recovery. Norm approximation gives
agreement on full nonnegative overlaps. The checked nonnegative-action
gluing theorem then supplies one common complex action domain.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- One open complex native action/mean domain contains the data of
EVERY original real H1 profile, with one common l1-valued holomorphic
forward NLS action factor and global recovery on all those profiles. -/
theorem exists_global_miura_original_NLS_action_factor :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧
        (∀ a : MiuraRealSobolevSource 1,
          miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a) ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ ∀ a : MiuraRealSobolevSource 1,
          F (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a)) =
            miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 a).val := by
  classical
  choose r hr g hg hrec using exists_miura_encoded_action_factor_ball
  have hpos (a : MiuraRealSobolevSource 1) : miuraH1EncodedActionParameters a ∈ Coeff.nonnegativeLocus 1 :=
    miuraExponentialActionParameters_physical_nonnegative (miuraPhysicalSobolevL2SourceInclusion 1 a)
  have hcompat (i j : MiuraRealSobolevSource 1) (q : Coeff 1)
      (hq : q ∈ ball (miuraH1EncodedActionParameters i) (r i) ∩ ball (miuraH1EncodedActionParameters j) (r j))
      (hqpos : q ∈ Coeff.nonnegativeLocus 1) : g i q = g j q := by
    apply Coeff.eq_of_finite_nonnegative_agreement (by simp : (1 : ℝ≥0∞) ≠ ⊤) (g i) (g j)
      _ (isOpen_ball.inter isOpen_ball) q hq hqpos (hg i q hq.1).continuousAt (hg j q hq.2).continuousAt
    intro b hb hbfin hbpos _
    obtain ⟨a,ha⟩ := exists_H1_profile_of_finite_encoded_actions b hbfin hbpos
    exact (hrec i a b hb.1 ha.symm).trans (hrec j a b hb.2 ha.symm).symm
  obtain ⟨G,hG,hlocal,_⟩ := Coeff.exists_analyticOnNhd_gluing_nonnegativeActions
    (p := 2) (q := 1) (by simp) miuraH1EncodedActionParameters r g hpos hg hcompat
  let W := ⋃ a : MiuraRealSobolevSource 1, ball (miuraH1EncodedActionParameters a) (r a)
  let V := miuraExponentialActionParameters ⁻¹' W
  have hE : Continuous miuraExponentialActionParameters :=
    continuous_iff_continuousAt.mpr (fun b => (analyticAt_miuraExponentialActionParameters b).continuousAt)
  have hall (a : MiuraRealSobolevSource 1) :
      miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a) ∈ V :=
    mem_iUnion.mpr ⟨a,mem_ball_self (hr a)⟩
  refine ⟨V,fun b => G (miuraExponentialActionParameters b),
    (isOpen_iUnion (fun _ => isOpen_ball)).preimage hE,hall,?_,?_⟩
  · intro b hb
    exact (hG _ hb).comp (analyticAt_miuraExponentialActionParameters b)
  · intro a
    change G (miuraH1EncodedActionParameters a) = _
    exact (hlocal a (mem_ball_self (hr a))).trans
      (hrec a a _ (mem_ball_self (hr a)) (miuraLogActionParameters_exponential_physical _))

theorem miuraPhysicalSobolevL2SourceInclusion_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (miuraPhysicalSobolevL2SourceInclusion 1 ⟨miuraH1SobolevEquiv a,miuraH1SobolevReal a ha⟩).val = scalarInclusion a := by
  ext j
  rw [miuraPhysicalSobolevL2SourceInclusion_apply,miuraH1SobolevEquiv_apply,scalarInclusion_apply]

/-- The same global factor on the literal original H1 scalar domain. -/
theorem exists_global_miura_original_H1_NLS_action_factor :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧
        (∀ a : ScalarDomain 2, (∀ j, a.val j = conj (a.val (-j))) → miuraL2ActionMeanMap (scalarInclusion a) ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ ∀ a : ScalarDomain 2, ∀ _ha : ∀ j, a.val j = conj (a.val (-j)),
          F (miuraL2ActionMeanMap (scalarInclusion a)) = miuraOriginalNLSActionSequence (scalarInclusion a) := by
  obtain ⟨V,F,hV,hall,hF,hrec⟩ := exists_global_miura_original_NLS_action_factor
  refine ⟨V,F,hV,?_,hF,?_⟩
  · intro a ha
    have h := hall ⟨miuraH1SobolevEquiv a,miuraH1SobolevReal a ha⟩
    change miuraL2ActionMeanMap _ ∈ V at h
    rwa [miuraPhysicalSobolevL2SourceInclusion_H1 a ha] at h
  · intro a ha
    have h := hrec ⟨miuraH1SobolevEquiv a,miuraH1SobolevReal a ha⟩
    change F (miuraL2ActionMeanMap _) = miuraOriginalNLSActionSequence _ at h
    rwa [miuraPhysicalSobolevL2SourceInclusion_H1 a ha] at h

end NLS.MKdV
