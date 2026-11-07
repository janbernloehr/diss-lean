import NLS.Articles.KdVKdV2Frequencies.SharpSobolevActionFrequencyBounds
import NLS.SequenceSpaces.LeadingActionFrequencyTransfer

/-! Corollary 1.5(i)'s uncorrected-frequency estimate in normalized
actions. Its big-O constant is locally uniform at ALL positive labels;
the little-o assertion is pointwise, as required for the leading action. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_uncorrected_sobolev_action_frequency_decay
    (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t) (ht1 : t≤1)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : Coeff 1) (ha₀ : a₀∈Coeff.nonnegativeLocus 1) :
    let κ := normalizedSobolevWeakActionInclusion (2*t-1) (by linarith)
    ∃ U : Set (Coeff 1), IsOpen U ∧ a₀∈U ∧ U⊆κ ⁻¹' V ∧
      ∃ B : ℝ, 0≤B ∧ (∀ a∈U, ∀ n : ℕ+, Weight.sobolev (2*t-1) (n:ℤ)*‖G n (κ a)‖≤B) ∧
        (t<1 → ∀ a∈U, Tendsto (fun m : ℕ => Weight.sobolev (2*t-1) ((m+1:ℕ):ℤ)*
          ‖G ⟨m+1,by omega⟩ (κ a)‖) atTop (𝓝 0)) := by
  intro κ
  let θ := min t (2/3)
  have hθ : 0≤θ := le_min ht (by norm_num)
  have hθ1 : θ≤2/3 := min_le_right _ _
  have hθt : θ≤t := min_le_left _ _
  have hweight : 2*t-1≤3*θ-1 := by
    by_cases h : t≤2/3
    · dsimp only [θ];rw [min_eq_left h];linarith
    · dsimp only [θ];rw [min_eq_right (by linarith : (2:ℝ)/3≤t)];linarith
  obtain ⟨U₀,hU₀,haU₀,hUV,_,K,M,hM,hb,hd⟩ := exists_sharp_sobolev_action_frequency_bounds
    D t θ (2*t-1) ht hθ hθ1 hθt rfl G V hV hCV hG hrec a₀ ha₀
  let f := fun n a => G n (κ a)
  let g := normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G
  have hf (n : ℕ+) : ContinuousOn (f n) U₀ := by
    have han : AnalyticOnNhd ℂ (f n) U₀ :=
      fun a ha => ((hG n (κ a) (hUV ha)).comp (κ.analyticAt a))
    exact han.continuousOn
  have htail : t<1 → 2*t-1<3*θ-1 ∨ ∀ a∈U₀,
      Tendsto (fun m : ℕ => Weight.sobolev (3*θ-1) ((m+1:ℕ):ℤ)*‖g ⟨m+1,by omega⟩ a‖) atTop (𝓝 0) := by
    intro htlt
    by_cases hl : t<2/3
    · exact Or.inr (hd (hθt.trans_lt hl))
    · apply Or.inl
      have heθ : θ=2/3 := min_eq_right (by linarith)
      rw [heθ]
      linarith
  obtain ⟨U,hU,haU,hUU,B,hB,hbU,hdU⟩ := Coeff.exists_uncorrected_frequency_decay_of_action_bounds
    actionIndexEquiv U₀ hU₀ a₀ haU₀ (2*t-1) (3*θ-1) hweight f g (fun _ _ => rfl)
    hf K M hM hb (t<1) htail
  exact ⟨U,hU,haU,(fun _ ha => hUV (hUU ha)),B,hB,hbU,hdU⟩

end NLS.Articles.KdVKdV2Frequencies
