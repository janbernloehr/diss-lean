import NLS.MKdV.MiuraNativeHamiltonianEncodedFactors
import NLS.SequenceSpaces.NonnegativeActionGluing
import NLS.ComplexAnalysis.AnalyticFactorPullback

/-! # Global holomorphic action normal forms for the independent Hill hierarchy

For each s>=1 one common open complex native action/mean domain contains
the data of every original real H^s profile. One holomorphic scalar factor
recovers the independent physical spectral Hamiltonian K_(s+1) everywhere.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

theorem exists_global_normalized_native_miuraHamiltonian_action_factor (s : ℕ) (hs : 1 ≤ s) :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → ℂ,
      IsOpen V ∧ (∀ a : MiuraRealSobolevSource s, miuraNormalizedNativeActionMeanMap s a.val ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ ∀ a : MiuraRealSobolevSource s,
          F (miuraNormalizedNativeActionMeanMap s a.val) = miuraSpectralHillHamiltonian s a.val := by
  classical
  choose r hr g hg hrec using exists_nativeHamiltonian_encoded_action_factor_ball s hs
  have hcompat (i j : MiuraRealSobolevSource s) (q : Coeff 1)
      (hq : q ∈ ball (miuraNativeEncodedActionParameters s i) (r i) ∩
        ball (miuraNativeEncodedActionParameters s j) (r j)) (hpos : q ∈ Coeff.nonnegativeLocus 1) : g i q = g j q := by
    obtain ⟨a,ha⟩ := exists_native_profile_of_nonnegative_encoded s hs q hpos
    exact (hrec i a q hq.1 ha.symm).trans (hrec j a q hq.2 ha.symm).symm
  obtain ⟨G,hG,hlocal,_⟩ := Coeff.exists_analyticOnNhd_gluing_nonnegativeActions
    (p := 2) (q := 1) (by simp) (miuraNativeEncodedActionParameters s) r g
      (miuraNativeEncodedActionParameters_nonnegative s) hg hcompat
  let W := ⋃ a : MiuraRealSobolevSource s, ball (miuraNativeEncodedActionParameters s a) (r a)
  let V := miuraExponentialActionParameters ⁻¹' W
  have hE : Continuous miuraExponentialActionParameters :=
    continuous_iff_continuousAt.mpr (fun b => (analyticAt_miuraExponentialActionParameters b).continuousAt)
  have hall (a : MiuraRealSobolevSource s) : miuraNormalizedNativeActionMeanMap s a.val ∈ V :=
    mem_iUnion.mpr ⟨a,mem_ball_self (hr a)⟩
  refine ⟨V,fun b => G (miuraExponentialActionParameters b),
    (isOpen_iUnion (fun _ => isOpen_ball)).preimage hE,hall,?_,?_⟩
  · intro b hb
    exact (hG _ hb).comp (analyticAt_miuraExponentialActionParameters b)
  · intro a
    change G (miuraNativeEncodedActionParameters s a) = _
    exact (hlocal a (mem_ball_self (hr a))).trans
      (hrec a a _ (mem_ball_self (hr a)) (miuraNativeEncodedActionParameters_decode s a))

/-- A single holomorphic K_(s+1) normal form on an open complex domain
containing the native physical action/mean data of every real H^s profile. -/
theorem exists_global_native_miuraHamiltonian_action_factor (s : ℕ) (hs : 1 ≤ s) :
    ∃ V : Set (MiuraNativeActionMeanTarget s), ∃ F : MiuraNativeActionMeanTarget s → ℂ,
      IsOpen V ∧ (∀ a : MiuraRealSobolevSource s, miuraNativeActionMeanMap s a.val ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ ∀ a : MiuraRealSobolevSource s,
          F (miuraNativeActionMeanMap s a.val) = miuraSpectralHillHamiltonian s a.val := by
  exact NLS.ComplexAnalysis.exists_analytic_factor_pullback
    (miuraNativeActionMeanEquiv s).toContinuousLinearMap
    (fun a : MiuraRealSobolevSource s => miuraNativeActionMeanMap s a.val)
    (fun a : MiuraRealSobolevSource s => miuraSpectralHillHamiltonian s a.val)
    (exists_global_normalized_native_miuraHamiltonian_action_factor s hs)

end NLS.MKdV
