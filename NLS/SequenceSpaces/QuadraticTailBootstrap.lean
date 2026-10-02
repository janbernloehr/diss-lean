import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Decay from a quadratic tail recurrence

A nonnegative tail tending to zero eventually makes its own quadratic
term a strict linear contraction. A geometrically decaying forcing
term then yields geometric decay at every slower rate.
-/

noncomputable section
open Filter Topology
namespace NLS

/-- Bootstrap a vanishing sequence through a quadratic recurrence.
The starting index may move; no initial quantitative decay is assumed. -/
theorem exists_geometric_bound_of_quadratic_recurrence
    (u : ℕ → ℝ) (A B r q : ℝ)
    (hu : ∀ k, 0 ≤ u k) (hlim : Tendsto u atTop (𝓝 0))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r) (hrq : r < q) (_hq : q < 1)
    (hrec : ∀ k, u (k+1) ≤ A*r^k+B*(u k)^2) :
    ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, u (K+k) ≤ C*q^k := by
  have hq0 : 0 < q := hr.trans hrq
  let s := q/2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsq : s < q := by dsimp [s]; linarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hlim.eventually_lt_const (show 0 < s/(B+1) by positivity))
  have hsmall (k : ℕ) : B*u (K+k) ≤ s := by
    have h := hK (K+k) (by omega)
    have hh := (lt_div_iff₀ (show 0 < B+1 by positivity)).mp h
    nlinarith [hu (K+k)]
  let C := max (u K) (A*r^K/(q-s))
  have hC : 0 ≤ C := (hu K).trans (le_max_left _ _)
  have hforce : A*r^K ≤ C*(q-s) := by
    exact (div_le_iff₀ (sub_pos.mpr hsq)).mp (le_max_right _ _)
  refine ⟨K,C,hC,?_⟩
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero, pow_zero, mul_one] using (le_max_left (u K) (A*r^K/(q-s)))
  | succ k ih =>
    have hquad : B*(u (K+k))^2 ≤ s*u (K+k) := by
      nlinarith [mul_le_mul_of_nonneg_right (hsmall k) (hu (K+k))]
    calc
      u (K+(k+1)) ≤ A*r^(K+k)+B*(u (K+k))^2 := by simpa [Nat.add_assoc] using hrec (K+k)
      _ ≤ A*r^K*q^k+s*(C*q^k) := by
        rw [pow_add]
        have hp := pow_le_pow_left₀ hr.le hrq.le k
        have hterm := mul_le_mul_of_nonneg_left hp (mul_nonneg hA (pow_nonneg hr.le K))
        have hsecond := hquad.trans (mul_le_mul_of_nonneg_left ih hs.le)
        nlinarith
      _ ≤ C*(q-s)*q^k+s*(C*q^k) := by
        gcongr
      _ = C*q^(k+1) := by rw [pow_succ]; ring

/-- A tail recurrence at quadrupled cutoffs gives geometric decay
along a geometric sequence of cutoffs, with any slower rate. -/
theorem exists_four_adic_bound_of_quadratic_tail
    (v : ℕ → ℝ) (A B α q : ℝ) (N₀ : ℕ)
    (hv : ∀ N, 0 ≤ v N) (hlim : Tendsto v atTop (𝓝 0))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 < α)
    (hq : (4 : ℝ)^(-α) < q) (hq1 : q < 1)
    (hrec : ∀ N : ℕ, N₀ ≤ N → v (4*N) ≤ A/(4*N : ℝ)^α+B*(v N)^2) :
    ∃ M : ℕ, 0 < M ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, v (4^k*M) ≤ C*q^k := by
  let L := N₀+1
  have hL : 0 < L := by dsimp [L]; omega
  let u (k : ℕ) := v (4^k*L)
  have hcut : Tendsto (fun k : ℕ => 4^k*L) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right (4^k) hL)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 4))
  have hur (k : ℕ) : u (k+1) ≤ A*((4 : ℝ)^(-α))^k+B*(u k)^2 := by
    have hNk : N₀ ≤ 4^k*L := by
      have hpow : 1 ≤ (4 : ℕ)^k := Nat.one_le_pow k 4 (by norm_num)
      dsimp [L]
      nlinarith
    have h := hrec (4^k*L) hNk
    have hbase : (4 : ℝ)^k ≤ 4*(4^k*L : ℕ) := by
      have hpow : 0 ≤ (4 : ℝ)^k := by positivity
      have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
      push_cast
      nlinarith
    have hp0 : 0 < (4 : ℝ)^k := by positivity
    have hinv : 1/(4*(4^k*L : ℕ) : ℝ)^α ≤ ((4 : ℝ)^(-α))^k := by
      rw [Real.rpow_pow_comm (by norm_num), Real.rpow_neg hp0.le, one_div]
      exact inv_le_inv₀ (Real.rpow_pos_of_pos (hp0.trans_le hbase) _) (Real.rpow_pos_of_pos hp0 _) |>.mpr
        (Real.rpow_le_rpow hp0.le hbase hα.le)
    have hterm := mul_le_mul_of_nonneg_left hinv hA
    have hfinal := h.trans (add_le_add (show A/(4*(4^k*L : ℕ) : ℝ)^α ≤ A*((4 : ℝ)^(-α))^k by
      simpa only [div_eq_mul_inv, one_div, one_mul] using hterm) le_rfl)
    simpa only [u,pow_succ,mul_assoc,mul_left_comm] using hfinal
  obtain ⟨K,C,hC,hbound⟩ := exists_geometric_bound_of_quadratic_recurrence u A B
    ((4 : ℝ)^(-α)) q (fun k => hv _) (hlim.comp hcut) hA hB
    (Real.rpow_pos_of_pos (by norm_num) _) hq hq1 hur
  refine ⟨4^K*L,by positivity,C,hC,?_⟩
  intro k
  simpa only [u,pow_add,mul_assoc,mul_comm (4^K),mul_left_comm] using hbound k

end NLS
