import NLS.MKdV.MiuraNativeHamiltonianFactorRecovery
import NLS.MKdV.MiuraNativeEncodedActionRealization

/-! # Native Hamiltonian factors on nonnegative-centered encoded action balls -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraNativeEncodedActionParameters (s : ℕ) (a : MiuraRealSobolevSource s) : Coeff 1 :=
  miuraExponentialActionParameters (miuraNormalizedNativeActionMeanMap s a.val)

theorem miuraNativeEncodedActionParameters_nonnegative (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraNativeEncodedActionParameters s a ∈ Coeff.nonnegativeLocus 1 := by
  change miuraExponentialActionParameters (miuraNormalizedNativeActionMeanMap s a.val) ∈ Coeff.nonnegativeLocus 1
  rw [← miuraNormalizedCartesian_actionMean s a.val a.property]
  exact miuraExponentialActionParameters_cartesian_nonnegative
    ⟨_,miuraSobolevNormalizedCartesianMap_real s a⟩

theorem miuraNativeEncodedActionParameters_slitPlane (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraNativeEncodedActionParameters s a 0 ∈ Complex.slitPlane := by
  change miuraExponentialActionParameters (miuraNormalizedNativeActionMeanMap s a.val) 0 ∈ Complex.slitPlane
  rw [← miuraNormalizedCartesian_actionMean s a.val a.property]
  exact miuraExponentialActionParameters_cartesian_slitPlane
    ⟨_,miuraSobolevNormalizedCartesianMap_real s a⟩

theorem miuraNativeEncodedActionParameters_decode (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraLogActionParameters (miuraNativeEncodedActionParameters s a) = miuraNormalizedNativeActionMeanMap s a.val := by
  change miuraLogActionParameters (miuraExponentialActionParameters (miuraNormalizedNativeActionMeanMap s a.val)) = _
  rw [← miuraNormalizedCartesian_actionMean s a.val a.property]
  exact miuraLogActionParameters_exponential_cartesian ⟨_,miuraSobolevNormalizedCartesianMap_real s a⟩

theorem exists_local_normalized_nativeHamiltonian_factor_global_recovery (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → ℂ,
      IsOpen V ∧ miuraNormalizedNativeActionMeanMap s a.val ∈ V ∧ AnalyticOnNhd ℂ F V ∧
        ∀ b : MiuraRealSobolevSource s, miuraNormalizedNativeActionMeanMap s b.val ∈ V →
          F (miuraNormalizedNativeActionMeanMap s b.val) = miuraSpectralHillHamiltonian s b.val := by
  obtain ⟨C⟩ := nonempty_miuraNativeCartesianChart s hs a
  exact C.exists_action_factor_global_recovery hs

theorem exists_nativeHamiltonian_encoded_action_factor_ball (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : Coeff 1 → ℂ,
      AnalyticOnNhd ℂ g (ball (miuraNativeEncodedActionParameters s a) r) ∧
        ∀ b : MiuraRealSobolevSource s, ∀ q ∈ ball (miuraNativeEncodedActionParameters s a) r,
          miuraLogActionParameters q = miuraNormalizedNativeActionMeanMap s b.val →
          g q = miuraSpectralHillHamiltonian s b.val := by
  obtain ⟨V,F,hV,haV,hF,hrec⟩ := exists_local_normalized_nativeHamiltonian_factor_global_recovery s hs a
  let S : Set (Coeff 1) := (fun q : Coeff 1 => q 0) ⁻¹' Complex.slitPlane
  have hS : IsOpen S := Complex.isOpen_slitPlane.preimage (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0).continuous
  have hD : AnalyticOnNhd ℂ miuraLogActionParameters S := fun q hq => analyticAt_miuraLogActionParameters q hq
  let U := S ∩ miuraLogActionParameters ⁻¹' V
  have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage hS hV
  have haU : miuraNativeEncodedActionParameters s a ∈ U := by
    refine ⟨miuraNativeEncodedActionParameters_slitPlane s a,?_⟩
    change miuraLogActionParameters (miuraNativeEncodedActionParameters s a) ∈ V
    rwa [miuraNativeEncodedActionParameters_decode]
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU _ haU
  refine ⟨r,hr,fun q => F (miuraLogActionParameters q),?_,?_⟩
  · intro q hq
    exact (hF _ (hball hq).2).comp (hD _ (hball hq).1)
  · intro b q hq he
    change F (miuraLogActionParameters q) = _
    rw [he]
    exact hrec b (he ▸ (hball hq).2)

end NLS.MKdV
