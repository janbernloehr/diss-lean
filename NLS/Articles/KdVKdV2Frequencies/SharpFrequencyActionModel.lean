import NLS.Articles.KdVKdV2Frequencies.SharpSobolevActionFrequencyBounds
import NLS.SequenceSpaces.LinearFrequencyDecayPullback

/-! Exact Banach action models inherit the SAME global weak
frequency bounds. The model space stays opaque under kernel checking. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_sharp_frequency_action_model_bounds
    (D : GlobalRoughAbelianForwardData) (t θ α : ℝ) (ht : 0≤t) (hθ : 0≤θ) (hθ1 : θ≤2/3) (hθt : θ≤t)
    (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (N : E →L[ℂ] Coeff 1) (f : ℕ+ → E → ℂ)
    (hfreq : ∀ n a, f n a=normalizedSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n (N a))
    (W : E → Coeff 1)
    (hweak : ∀ a, normalizedSobolevWeakActionInclusion α (by rw [← hαt];linarith) (N a)=W a)
    (a₀ : E) (ha₀ : N a₀∈Coeff.nonnegativeLocus 1) :
    ∃ U : Set E, IsOpen U ∧ a₀∈U ∧ (∀ a∈U, W a∈V) ∧
      (∀ n, AnalyticOnNhd ℂ (f n) U) ∧ ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        (∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev (3*θ-1) (n:ℤ)*‖f n a‖≤M) ∧
        (θ<2/3 → ∀ a∈U, Tendsto (fun n : ℕ => Weight.sobolev (3*θ-1) ((n+1:ℕ):ℤ)*
          ‖f ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  have hα : -1≤α := by rw [← hαt];linarith
  obtain ⟨T,hT,haT,hTV,hFa,K,M,hM,hb,hd⟩ := exists_sharp_sobolev_action_frequency_bounds
    D t θ α ht hθ hθ1 hθt hαt G V hV hCV hG hrec (N a₀) ha₀
  obtain ⟨U,hU,haU,hUT,hUa,hUb,hUd⟩ := Coeff.exists_linear_frequency_decay_pullback N f
    (normalizedSobolevRenormalizedFrequency α hα G) hfreq T hT hFa a₀ haT
    (Weight.sobolev (3*θ-1)) K M hb
  refine ⟨U,hU,haU,?_,hUa,K,M,hM,hUb,?_⟩
  · intro a ha
    rw [← hweak]
    exact hTV (hUT ha)
  · intro ht2
    exact hUd (hd ht2)

end NLS.Articles.KdVKdV2Frequencies
