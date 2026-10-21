import NLS.Fourier.ContinuousSynthesis
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Log

/-! # Ordinary convergence from summable dyadic-prefix bounds -/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Fourier

/-- Bounds for every dyadic prefix imply convergence along all ordinary cutoffs. -/
theorem exists_tendsto_of_dyadic_prefix_bounds
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (S : ℕ → E) (d : ℕ → ℝ) (hd : Summable d)
    (hb : ∀ k : ℕ, 1 ≤ k → ∀ M ≤ 2^k, ‖S (2^k+M)-S (2^k)‖ ≤ d k) :
    ∃ F : E, Tendsto S atTop (𝓝 F) := by
  let A : ℕ → E := fun k => S (2^(k+1))
  have hc : CauchySeq A := by
    apply cauchySeq_of_dist_le_of_summable (fun k => d (k+1))
    · intro k
      have h := hb (k+1) (by omega) (2^(k+1)) le_rfl
      simpa only [A,dist_eq_norm,norm_sub_rev,pow_succ,mul_two] using h
    · exact (summable_nat_add_iff 1).mpr hd
  obtain ⟨F,hF⟩ := cauchySeq_tendsto_of_complete hc
  let κ : ℕ → ℕ := fun n => Nat.log 2 n-1
  have ht : Tendsto κ atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (2^(k+1))] with n hn
    have h := Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn
    dsimp only [κ]
    omega
  have hD : Tendsto (fun n => dist (A (κ n)) (S n)) atTop (𝓝 0) := by
    have hz : Tendsto (fun n => d (Nat.log 2 n)) atTop (𝓝 0) := by
      apply hd.tendsto_atTop_zero.comp
      apply tendsto_atTop.2
      intro k
      filter_upwards [eventually_ge_atTop (2^k)] with n hn
      exact Nat.le_log_of_pow_le (by norm_num) hn
    apply squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) _ hz
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hk : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
    have hp := Nat.pow_log_le_self 2 hn0
    have hq := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    rw [pow_succ,mul_two] at hq
    have h := hb (Nat.log 2 n) hk (n-2^(Nat.log 2 n)) (by omega)
    rw [Nat.add_sub_of_le hp] at h
    simpa only [A,κ,Nat.sub_add_cancel hk,dist_eq_norm,norm_sub_rev] using h
  exact ⟨F,(hF.comp ht).congr_dist hD⟩

end NLS.Fourier
