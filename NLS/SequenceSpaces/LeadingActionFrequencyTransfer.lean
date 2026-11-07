import NLS.SequenceSpaces.FrequencyLeadingAction
import NLS.SequenceSpaces.UniformFrequencyFiniteHeads

/-! Uniform bounds and pointwise tails after removing an actual action
counterterm. The frequency families stay opaque under default checking. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem exists_uncorrected_frequency_decay_of_action_bounds
    (e : ℤ ≃ ℕ+) (U₀ : Set (Coeff 1)) (hU₀ : IsOpen U₀) (a₀ : Coeff 1) (ha₀ : a₀∈U₀)
    (α β : ℝ) (hαβ : α≤β) (f g : ℕ+ → Coeff 1 → ℂ)
    (he : ∀ n a, g n a=f n a+6*(a (e.symm n)/(Weight.sobolev α (n:ℤ):ℂ)))
    (hf : ∀ n, ContinuousOn (f n) U₀) (K : ℕ) (M : ℝ) (hM : 0≤M)
    (hb : ∀ a∈U₀, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev β (n:ℤ)*‖g n a‖≤M)
    (P : Prop) (htail : P → α<β ∨ ∀ a∈U₀,
      Tendsto (fun m : ℕ => Weight.sobolev β ((m+1:ℕ):ℤ)*‖g ⟨m+1,by omega⟩ a‖) atTop (𝓝 0)) :
    ∃ T : Set (Coeff 1), IsOpen T ∧ a₀∈T ∧ T⊆U₀ ∧ ∃ B : ℝ, 0≤B ∧
      (∀ a∈T, ∀ n : ℕ+, Weight.sobolev α (n:ℤ)*‖f n a‖≤B) ∧
      (P → ∀ a∈T, Tendsto (fun m : ℕ => Weight.sobolev α ((m+1:ℕ):ℤ)*‖f ⟨m+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  let U := U₀∩ball a₀ 1
  have hU : IsOpen U := hU₀.inter isOpen_ball
  have haU : a₀∈U := ⟨ha₀,mem_ball_self zero_lt_one⟩
  let R := ‖a₀‖+1
  have hR : 0≤R := by dsimp only [R];positivity
  have hnorm (a : Coeff 1) (ha : a∈U) : ‖a‖≤R := by
    have hd : ‖a-a₀‖≤1 := by simpa only [dist_eq_norm] using (mem_ball.mp ha.2).le
    have hn := norm_add_le (a-a₀) a₀
    rw [sub_add_cancel] at hn
    dsimp only [R]
    linarith
  have hremove (a : Coeff 1) (n : ℕ+) :
      Weight.sobolev α (n:ℤ)*‖f n a‖≤Weight.sobolev α (n:ℤ)*‖g n a‖+6*‖a (e.symm n)‖ := by
    rw [he]
    exact weighted_remove_linear_counterterm_bound _ 6 ((Weight.sobolev α).positive (n:ℤ)) (by norm_num) _ _
  have hbound : ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
      Weight.sobolev α (n:ℤ)*‖f n a‖≤M+6*R := by
    intro a ha n hn
    apply (hremove a n).trans
    have hc := (mul_le_mul_of_nonneg_right (Weight.sobolev_mono hαβ (n:ℤ)) (norm_nonneg (g n a))).trans (hb a ha.1 n hn)
    have hcoord := (lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞)≠0) a (e.symm n)).trans (hnorm a ha)
    linarith
  obtain ⟨T,hT,haT,hTU,B,hB,hall⟩ := exists_uniform_all_frequency_bound_of_tail U hU a₀ haU f
    (fun n => (hf n).mono inter_subset_left) (Weight.sobolev α)
    (fun n => ((Weight.sobolev α).positive (n:ℤ)).le) K (M+6*R) (by positivity) hbound
  refine ⟨T,hT,haT,(fun _ ha => (hTU ha).1),B,hB,hall,?_⟩
  intro hP a ha
  have hcorr : Tendsto (fun m : ℕ => Weight.sobolev α ((m+1:ℕ):ℤ)*‖g ⟨m+1,by omega⟩ a‖) atTop (𝓝 0) := by
    rcases htail hP with hstrict|hpoint
    · exact tendsto_positive_weighted_of_uniform_tail U₀ g (Weight.sobolev α)
        (fun n => ((Weight.sobolev α).positive (n:ℤ)).le)
        (exists_uniform_strict_sobolev_frequency_tail U₀ g α β hstrict K M hM hb) a (hTU ha).1
    · exact tendsto_positive_weighted_sobolev_mono α β hαβ (fun n : ℕ+ => g n a) (hpoint a (hTU ha).1)
  have hh := hcorr.add ((tendsto_norm_enumerated_positive e a).const_mul 6)
  rw [zero_add,mul_zero] at hh
  exact squeeze_zero (fun _ => mul_nonneg ((Weight.sobolev α).positive _).le (norm_nonneg _))
    (fun m => hremove a ⟨m+1,by omega⟩) hh

end NLS.Coeff
