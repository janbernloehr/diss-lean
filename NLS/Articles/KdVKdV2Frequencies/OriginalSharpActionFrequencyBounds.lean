import NLS.Articles.KdVKdV2Frequencies.SharpFrequencyActionModel
import NLS.Articles.KdVKdV2Frequencies.IntermediateFrequencyRawTargets
import NLS.SequenceSpaces.LinearFrequencyDecayPullback

/-! Sharp FULL corrected-frequency bounds in the ORIGINAL raw
weighted action norm, with the SAME global weak scalar frequency. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def originalSobolevRenormalizedFrequency (α : ℝ) (hα : -1≤α)
    (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (a : WeightedCoeff (Weight.sobolev α) 1) : ℂ :=
  G n (weakActionEnumeration (weakActionNormalization (WeightedCoeff.sobolevInclusion hα a)))+
    6*a.val (n:ℤ)

theorem originalSobolevRenormalizedFrequency_eq_normalized
    (α : ℝ) (hα : -1≤α) (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+)
    (a : WeightedCoeff (Weight.sobolev α) 1) :
    originalSobolevRenormalizedFrequency α hα G n a=
      normalizedSobolevRenormalizedFrequency α hα G n (sobolevActionEnumeration α a) := by
  rw [originalSobolevRenormalizedFrequency,normalizedSobolevRenormalizedFrequency,
    normalizedSobolevWeakActionInclusion_enumeration,sobolevActionEnumeration_apply,
    Equiv.apply_symm_apply,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

theorem exists_original_sharp_action_frequency_bounds
    (D : GlobalRoughAbelianForwardData) (t θ α : ℝ) (ht : 0≤t) (hθ : 0≤θ) (hθ1 : θ≤2/3) (hθt : θ≤t)
    (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : WeightedCoeff (Weight.sobolev α) 1) (ha₀ : a₀∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1), IsOpen U ∧ a₀∈U ∧
      (∀ a∈U, weakActionEnumeration (weakActionNormalization
        (WeightedCoeff.sobolevInclusion (by rw [← hαt];linarith : -1≤α) a))∈V) ∧
      (∀ n, AnalyticOnNhd ℂ (originalSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n) U) ∧
      ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        (∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev (3*θ-1) (n:ℤ)*
          ‖originalSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n a‖≤M) ∧
        (θ<2/3 → ∀ a∈U, Tendsto (fun n : ℕ => Weight.sobolev (3*θ-1) ((n+1:ℕ):ℤ)*
          ‖originalSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  have hα : -1≤α := by rw [← hαt];linarith
  exact exists_sharp_frequency_action_model_bounds D t θ α ht hθ hθ1 hθt hαt G V hV hCV hG hrec
    (sobolevActionEnumeration α) (originalSobolevRenormalizedFrequency α hα G)
    (fun n a => originalSobolevRenormalizedFrequency_eq_normalized α hα G n a)
    (fun a => weakActionEnumeration (weakActionNormalization (WeightedCoeff.sobolevInclusion hα a)))
    (fun a => normalizedSobolevWeakActionInclusion_enumeration α hα a) a₀
    (sobolevActionEnumeration_nonnegative α a₀ ha₀.1)

end NLS.Articles.KdVKdV2Frequencies
