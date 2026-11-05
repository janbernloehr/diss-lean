import NLS.KdV.HillLocallyUniformActionTails

/-! # Continuity of the total weighted real Hill action

The common high action-gap estimate and the Fourier budget make the
summed tail small on a neighborhood. Continuity of individual actions
then gives continuity of their total weighted sum, including collisions.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

def hillWeightedActionTerm (w : SpectralWeight) (p : RealHillWeightedPotential w) (n : ℕ) : ℝ :=
  w (2 * (n : ℤ))^2 * (2 * Real.pi * (n : ℝ)) * hillPeriodOneAction w p.val p.property n

theorem hillWeightedActionTerm_nonneg (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (n : ℕ) : 0 ≤ hillWeightedActionTerm w p n := by
  by_cases hn : n = 0
  · subst n
    simp [hillWeightedActionTerm]
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
      (hillPeriodOneAction_nonneg w p.val p.property n (by omega))

theorem summable_hillWeightedActionTerm (w : SpectralWeight) (p : RealHillWeightedPotential w) :
    Summable (hillWeightedActionTerm w p) := by
  have hs : Summable (fun k : ℕ => hillWeightedActionTerm w p (k+1)) := by
    simpa only [hillWeightedActionTerm] using
      summable_hillPeriodOneAction_weighted w p.val p.property
  exact (summable_nat_add_iff 1).mp hs

theorem exists_hillWeightedActionTerm_small_tail
    (w : SpectralWeight) (q : RealHillWeightedPotential w) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set (RealHillWeightedPotential w),
      2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧ ∀ p ∈ U,
      Summable (fun k : ℕ => hillWeightedActionTerm w p (k+N)) ∧
        (∑' k : ℕ, hillWeightedActionTerm w p (k+N)) ≤ ε := by
  obtain ⟨N₀, U₀, hN₀, hU₀, hqU₀, htail⟩ :=
    exists_hillPeriodOneAction_local_weighted_tail_bound w q
  obtain ⟨A, hA⟩ := exists_nat_ge (16 * (‖q.val‖ + 1))
  have hbudget : ∀ᶠ N : ℕ in atTop, hillWeightedActionTailBudget w N q.val < ε :=
    (tendsto_hillWeightedActionTailBudget w q.val).eventually (gt_mem_nhds hε)
  obtain ⟨N, hNN₀, hNA, hBN⟩ :=
    ((eventually_ge_atTop N₀).and ((eventually_ge_atTop A).and hbudget)).exists
  have hB : Continuous (fun p : RealHillWeightedPotential w => hillWeightedActionTailBudget w N p.val) :=
    (continuous_hillWeightedActionTailBudget w N).comp continuous_subtype_val
  let U : Set (RealHillWeightedPotential w) := U₀ ∩
    ({p | ‖p.val‖ < ‖q.val‖ + 1} ∩ {p | hillWeightedActionTailBudget w N p.val < ε})
  have hU : IsOpen U := hU₀.inter
    ((isOpen_lt continuous_subtype_val.norm continuous_const).inter
      (isOpen_lt hB continuous_const))
  refine ⟨N, U, hN₀.trans hNN₀, hU, ⟨hqU₀, by dsimp; linarith, hBN⟩, ?_⟩
  intro p hp
  have hpn : ‖p.val‖ < ‖q.val‖ + 1 := hp.2.1
  have hcut : 16 * ‖p.val‖ ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hpn.le (by norm_num : (0 : ℝ) ≤ 16)).trans
      (hA.trans (by exact_mod_cast hNA))
  obtain ⟨hs, hb⟩ := htail p hp.1 N hNN₀ hcut
  refine ⟨by simpa only [hillWeightedActionTerm] using hs, ?_⟩
  rw [← hillWeightedActionTailBudget_eq w N p.val] at hb
  have hb' : (∑' k : ℕ, hillWeightedActionTerm w p (k+N)) ≤
      hillWeightedActionTailBudget w N p.val := by
    simpa only [hillWeightedActionTerm] using hb
  exact hb'.trans hp.2.2.le

theorem continuous_hillPeriodOneAction (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun p : RealHillWeightedPotential w => hillPeriodOneAction w p.val p.property n) := by
  have hQ : Continuous (fun p : RealHillWeightedPotential w => hillPeriodOneUnitPotential w p.val) :=
    (continuous_hillPeriodOneUnitPotential w).comp continuous_subtype_val
  have h := continuous_hillRealGapIntegral_family
    (fun p : RealHillWeightedPotential w => hillPeriodOneUnitPotential w p.val) hQ
    (fun p => hillPeriodOneUnitPotential_even w p.val)
    (fun p => hillPeriodOneUnitPotential_real w p.val p.property) n hn 0
  simpa only [hillPeriodOneAction] using h

theorem continuous_hillWeightedActionTerm (w : SpectralWeight) (n : ℕ) :
    Continuous (fun p : RealHillWeightedPotential w => hillWeightedActionTerm w p n) := by
  by_cases hn : n = 0
  · subst n
    simp only [hillWeightedActionTerm, Nat.cast_zero, mul_zero, zero_mul]
    exact continuous_const
  · simpa only [hillWeightedActionTerm] using
      (continuous_hillPeriodOneAction w n (by omega)).const_mul
        (w (2 * (n : ℤ))^2 * (2 * Real.pi * (n : ℝ)))

theorem continuous_tsum_hillWeightedActionTerm (w : SpectralWeight) :
    Continuous (fun p : RealHillWeightedPotential w => ∑' n : ℕ, hillWeightedActionTerm w p n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply continuousAt_tsum_of_locally_small_nat_tails (hillWeightedActionTerm w) q
    (summable_hillWeightedActionTerm w) (fun n => (continuous_hillWeightedActionTerm w n).continuousAt)
  intro ε hε
  obtain ⟨N, U, _, hU, hqU, htail⟩ := exists_hillWeightedActionTerm_small_tail w q ε hε
  refine ⟨N, ?_⟩
  filter_upwards [hU.mem_nhds hqU] with p hp
  have hnonneg : 0 ≤ ∑' k : ℕ, hillWeightedActionTerm w p (k+N) :=
    tsum_nonneg (fun k => hillWeightedActionTerm_nonneg w p (k+N))
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (htail p hp).2

end NLS.KdV
