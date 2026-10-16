import NLS.SequenceSpaces.QuadraticTailBootstrap
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Summability for a forced quadratic tail recurrence

A vanishing nonnegative tail with summable geometrically weighted forcing
has the same weighted summability. Finite exceptional terms are absorbed
into the forcing; no loss in the prescribed geometric weight occurs.
-/

noncomputable section
open Filter Topology
namespace NLS

/-- A nonnegative sequence with summable forcing and a strict linear contraction
is summable. The coefficient need not be nonnegative. -/
theorem summable_of_nonnegative_linear_recurrence
    (u f : ℕ → ℝ) (q : ℝ) (hu : ∀ k, 0 ≤ u k) (hf : ∀ k, 0 ≤ f k)
    (hfs : Summable f) (hq : q < 1)
    (hrec : ∀ k, u (k+1) ≤ f k+q*u k) : Summable u := by
  apply summable_of_sum_range_le hu (c := ((∑' k, f k)+u 0)/(1-q))
  intro N
  have h := Finset.sum_le_sum (s := Finset.range N) (fun k _ => hrec k)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at h
  have hshift : (∑ k ∈ Finset.range N, u (k+1))+u 0 =
      (∑ k ∈ Finset.range N, u k)+u N := by
    rw [← Finset.sum_range_succ',Finset.sum_range_succ]
  have hfbound : (∑ k ∈ Finset.range N, f k) ≤ ∑' k, f k :=
    hfs.sum_le_tsum (Finset.range N) (fun k _ => hf k)
  apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
  nlinarith [hu N]

/-- Exact geometric weighted summability under a quadratic recurrence.
The quadratic coefficient may be any real number. -/
theorem summable_geometric_weight_of_forced_quadratic_recurrence
    (u f : ℕ → ℝ) (B r : ℝ) (hu : ∀ k, 0 ≤ u k) (hf : ∀ k, 0 ≤ f k)
    (hlim : Tendsto u atTop (𝓝 0)) (hr : 0 < r)
    (hfs : Summable (fun k => r^k*f k))
    (hrec : ∀ k, u (k+1) ≤ f k+B*(u k)^2) :
    Summable (fun k => r^k*u k) := by
  have hlimB : Tendsto (fun k => r*B*u k) atTop (𝓝 0) := by
    simpa using hlim.const_mul (r*B)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hlimB.eventually_lt_const (by norm_num : (0:ℝ)<1/2))
  let v := fun k => r^k*u k
  let F := fun k => r^(k+1)*f k + if k<K then v (k+1) else 0
  have hv (k : ℕ) : 0 ≤ v k := mul_nonneg (pow_nonneg hr.le k) (hu k)
  have hF (k : ℕ) : 0 ≤ F k := by
    dsimp [F]
    split_ifs
    · exact add_nonneg (mul_nonneg (pow_nonneg hr.le _) (hf k)) (hv _)
    · exact add_nonneg (mul_nonneg (pow_nonneg hr.le _) (hf k)) le_rfl
  have hFsum : Summable F := by
    have hfirst : Summable (fun k => r^(k+1)*f k) := by
      apply (hfs.mul_left r).congr
      intro k
      rw [pow_succ]
      ring
    exact hfirst.add (summable_of_ne_finset_zero (s := Finset.range K) (by
      intro k hk
      simp only [Finset.mem_range] at hk
      simp only [if_neg hk]))
  apply summable_of_nonnegative_linear_recurrence v F (1/2) hv hF hFsum (by norm_num)
  intro k
  by_cases hk : k<K
  · dsimp [F]
    rw [if_pos hk]
    nlinarith [hv k, mul_nonneg (pow_nonneg hr.le (k+1)) (hf k)]
  · have hsmall : r*B*u k ≤ 1/2 := (hK k (by omega)).le
    have hquad : r^(k+1)*(B*(u k)^2) ≤ (1/2)*v k := by
      calc
        _ = (r*B*u k)*v k := by dsimp [v]; rw [pow_succ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (hv k)
    have h := mul_le_mul_of_nonneg_left (hrec k) (pow_nonneg hr.le (k+1))
    change r^(k+1)*u (k+1) ≤ _ at h
    dsimp [F]
    rw [if_neg hk,add_zero]
    change r^(k+1)*u (k+1) ≤ _
    nlinarith

/-- Gap forcing sampled at quadrupled cutoffs transfers its exact geometric
weight to a vanishing tail, below the algebraic forcing rate. -/
theorem summable_four_adic_of_forced_quadratic_tail
    (v g : ℕ → ℝ) (A B α r : ℝ) (N₀ M : ℕ)
    (hv : ∀ N, 0 ≤ v N) (hg : ∀ N, 0 ≤ g N)
    (hlim : Tendsto v atTop (𝓝 0)) (hA : 0 ≤ A) (hα : 0 < α)
    (hr : 0 < r) (hrα : r*(4:ℝ)^(-α) < 1) (hM : 0 < M) (hNM : N₀ ≤ M)
    (hgs : Summable (fun k => r^k*g (4*(4^k*M))))
    (hrec : ∀ N : ℕ, N₀ ≤ N → v (4*N) ≤ g (4*N)+A/(4*N:ℝ)^α+B*(v N)^2) :
    Summable (fun k => r^k*v (4^k*M)) := by
  let u := fun k => v (4^k*M)
  let f := fun k => g (4*(4^k*M))+A*((4:ℝ)^(-α))^k
  have hcut : Tendsto (fun k : ℕ => 4^k*M) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right (4^k) hM)
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℕ)<4))
  have hfs : Summable (fun k => r^k*f k) := by
    have hgeo := (summable_geometric_of_lt_one
      (mul_nonneg hr.le (Real.rpow_pos_of_pos (by norm_num) (-α)).le) hrα).mul_left A
    apply (hgs.add hgeo).congr
    intro k
    dsimp [f]
    rw [mul_pow]
    ring
  apply summable_geometric_weight_of_forced_quadratic_recurrence u f B r
    (fun k => hv _) (fun k => add_nonneg (hg _) (mul_nonneg hA (by positivity)))
    (hlim.comp hcut) hr hfs
  intro k
  have hNk : N₀ ≤ 4^k*M := hNM.trans (by
    have hpow := Nat.one_le_pow k 4 (by norm_num)
    nlinarith)
  have hbase : (4:ℝ)^k ≤ 4*(4^k*M:ℕ) := by
    have hpow : 0 ≤ (4:ℝ)^k := by positivity
    have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
    push_cast
    nlinarith
  have hp0 : 0 < (4:ℝ)^k := by positivity
  have hinv : 1/(4*(4^k*M:ℕ):ℝ)^α ≤ ((4:ℝ)^(-α))^k := by
    rw [Real.rpow_pow_comm (by norm_num),Real.rpow_neg hp0.le,one_div]
    exact inv_le_inv₀ (Real.rpow_pos_of_pos (hp0.trans_le hbase) _) (Real.rpow_pos_of_pos hp0 _) |>.mpr
      (Real.rpow_le_rpow hp0.le hbase hα.le)
  have hterm : A/(4*(4^k*M:ℕ):ℝ)^α ≤ A*((4:ℝ)^(-α))^k := by
    simpa only [div_eq_mul_inv,one_div,one_mul] using mul_le_mul_of_nonneg_left hinv hA
  have h := (hrec (4^k*M) hNk).trans (add_le_add (add_le_add le_rfl hterm) le_rfl)
  simpa only [u,f,pow_succ,mul_assoc,mul_left_comm] using h
end NLS
