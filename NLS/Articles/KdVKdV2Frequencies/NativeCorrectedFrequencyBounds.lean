import NLS.Articles.KdVKdV2Frequencies.NativeActionPhysicalCounterterm
import NLS.Articles.KdVKdV2Frequencies.SharpSobolevActionFrequencyBounds
import NLS.SequenceSpaces.CompactUniformFrequencyBounds

/-! The corrected actual frequency is O(1/n) locally in H^(-1/3),
and hence uniformly on compact sets in that weaker source norm. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def nativeCorrectedKdVFrequency (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (a : physicalRealDeletedSubmodule) : ℂ :=
  normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G n (nativeActionCoordinates D t ht a)

theorem nativeCorrectedKdVFrequency_eq_physical
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (a : physicalRealDeletedSubmodule) :
    nativeCorrectedKdVFrequency D t ht G n a=
      roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource t ht a)-
        8*(n:ℂ)^3*(Real.pi:ℂ)^3+
        6*D.roughActionCoordinate n (GlobalRoughAbelianForwardData.realNativeSource t ht a) := by
  unfold nativeCorrectedKdVFrequency normalizedSobolevRenormalizedFrequency
  rw [nativeActionCoordinates_weak,nativeActionCoordinates_raw_product]
  unfold roughKdVFrequency roughKdVFrequencyCorrection
  ring

theorem exists_local_native_corrected_frequency_bound
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : physicalRealDeletedSubmodule) :
    ∃ T : Set physicalRealDeletedSubmodule, IsOpen T ∧ a₀∈T ∧ ∃ B : ℝ, 0≤B ∧
      ∀ a∈T, ∀ n : ℕ+, Weight.sobolev 1 (n:ℤ)*
        ‖nativeCorrectedKdVFrequency D (2/3) (by norm_num) G n a‖≤B := by
  let N := nativeActionCoordinates D (2/3) (by norm_num)
  obtain ⟨U,hU,haU,_,hf,K,M,hM,hb,_⟩ := exists_sharp_sobolev_action_frequency_bounds
    D (2/3) (2/3) (2*(2/3)-1) (by norm_num) (by norm_num) le_rfl le_rfl rfl
    G V hV hCV hG hrec (N a₀) (nativeActionCoordinates_nonnegative D _ _ a₀)
  let f := normalizedSobolevRenormalizedFrequency (2*(2/3)-1) (by norm_num) G
  obtain ⟨S,hS,haS,_,B,hB,hall⟩ := Coeff.exists_uniform_all_frequency_bound_of_tail U hU (N a₀) haU f
    (fun n => (hf n).continuousOn) (Weight.sobolev 1)
    (fun n => ((Weight.sobolev 1).positive (n:ℤ)).le) K M hM (by
      simpa only [show (3:ℝ)*(2/3)-1=1 by norm_num] using hb)
  exact ⟨N ⁻¹' S,hS.preimage (continuous_nativeActionCoordinates D _ _),haS,B,hB,
    fun a ha n => hall (N a) ha n⟩

theorem exists_compact_native_corrected_frequency_bound
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (K : Set physicalRealDeletedSubmodule) (hK : IsCompact K) :
    ∃ B : ℝ, 0≤B ∧ ∀ a∈K, ∀ n : ℕ+, Weight.sobolev 1 (n:ℤ)*
      ‖nativeCorrectedKdVFrequency D (2/3) (by norm_num) G n a‖≤B :=
  Coeff.exists_uniform_frequency_bound_on_compact K hK
    (nativeCorrectedKdVFrequency D (2/3) (by norm_num) G) (Weight.sobolev 1)
    (fun a _ => exists_local_native_corrected_frequency_bound D G V hV hCV hG hrec a)

end NLS.Articles.KdVKdV2Frequencies
