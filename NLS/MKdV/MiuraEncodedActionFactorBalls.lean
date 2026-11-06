import NLS.MKdV.MiuraActionFactorGlobalRecovery
import NLS.MKdV.MiuraExponentialActionEncoding

/-! # Local factors on encoded nonnegative-centered action balls -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraH1EncodedActionParameters (a : MiuraRealSobolevSource 1) : Coeff 1 :=
  miuraExponentialActionParameters (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a))

theorem exists_miura_action_factor_global_H1_recovery (a : MiuraRealSobolevSource 1) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧ miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a) ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ b : MiuraRealSobolevSource 1,
          miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b) ∈ V →
          F (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b)) =
            miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val := by
  let u := miuraH1SobolevEquiv.symm a.val
  have hu : ∀ j, u.val j = conj (u.val (-j)) := by
    intro j
    simpa only [u,miuraH1SobolevEquiv_symm_apply] using a.property j
  obtain ⟨V,F,hV,huV,hF,hrec⟩ := exists_miura_action_factor_global_H1_recovery_at_H1 u hu
  have he : scalarInclusion u = (miuraPhysicalSobolevL2SourceInclusion 1 a).val := by
    ext j
    rw [scalarInclusion_apply,miuraH1SobolevEquiv_symm_apply,miuraPhysicalSobolevL2SourceInclusion_apply]
  rw [he] at huV
  exact ⟨V,F,hV,huV,hF,hrec⟩

/-- One encoded action ball recovers every original H1 representative
of any of its decoded physical action/mean data. -/
theorem exists_miura_encoded_action_factor_ball (a : MiuraRealSobolevSource 1) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : Coeff 1 → Coeff 1,
      AnalyticOnNhd ℂ g (ball (miuraH1EncodedActionParameters a) r) ∧
        ∀ b : MiuraRealSobolevSource 1, ∀ q ∈ ball (miuraH1EncodedActionParameters a) r,
          miuraLogActionParameters q = miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 b) →
          g q = miuraOriginalNLSActionSequence (miuraPhysicalSobolevL2SourceInclusion 1 b).val := by
  obtain ⟨V,F,hV,haV,hF,hrec⟩ := exists_miura_action_factor_global_H1_recovery a
  let S : Set (Coeff 1) := (fun q : Coeff 1 => q 0) ⁻¹' Complex.slitPlane
  have hS : IsOpen S := Complex.isOpen_slitPlane.preimage (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0).continuous
  have hD : AnalyticOnNhd ℂ miuraLogActionParameters S := fun q hq => analyticAt_miuraLogActionParameters q hq
  let U := S ∩ miuraLogActionParameters ⁻¹' V
  have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage hS hV
  have haU : miuraH1EncodedActionParameters a ∈ U := by
    refine ⟨miuraExponentialActionParameters_physical_slitPlane _,?_⟩
    change miuraLogActionParameters (miuraExponentialActionParameters
      (miuraRealL2ActionMeanMap (miuraPhysicalSobolevL2SourceInclusion 1 a))) ∈ V
    rwa [miuraLogActionParameters_exponential_physical]
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU _ haU
  refine ⟨r,hr,fun q => F (miuraLogActionParameters q),?_,?_⟩
  · intro q hq
    exact (hF _ (hball hq).2).comp (hD _ (hball hq).1)
  · intro b q hq he
    change F (miuraLogActionParameters q) = _
    rw [he]
    exact hrec b (he ▸ (hball hq).2)

end NLS.MKdV
