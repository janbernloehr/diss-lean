import NLS.ZakharovShabat.SobolevRiccatiApproximationUniform

/-! # The first term of every positive Riccati truncation

Each positive-order Riccati approximation equals -b*w up to a uniformly quadratic error on the original Sobolev ball.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Every positive-order Riccati approximation has the same first term
-b*w, with a quadratic remainder controlled by lower densities. -/
theorem norm_nlsRiccatiApproximation_first_order_le
    (a b : ℝ → ℂ) (N : ℕ) (hN : 1 ≤ N) (U : ℝ) (hU : 0 ≤ U)
    (hρ : ∀ j < N, ∀ x : ℝ, ‖nlsRiccatiDensity a b j x‖ ≤ U)
    (w : ℂ) (hw : ‖w‖ ≤ 1) (x : ℝ) :
    ‖nlsRiccatiApproximation a b N w x+b x*w‖ ≤ (N:ℝ)*U*‖w‖^2 := by
  cases N with
  | zero => omega
  | succ N =>
    have he : nlsRiccatiApproximation a b (N+1) w x+b x*w =
        ∑ k ∈ Finset.range N, nlsRiccatiDensity a b (k+1) x*w^((k+1)+1) := by
      rw [nlsRiccatiApproximation,Finset.sum_range_succ']
      simp only [zero_add,nlsRiccatiDensity_zero,Pi.neg_apply,pow_one]
      ring
    rw [he]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range N, U*‖w‖^2 := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul,norm_pow]
        exact mul_le_mul (hρ (k+1) (by have hh := Finset.mem_range.mp hk; omega) x)
          (pow_le_pow_of_le_one (norm_nonneg _) hw (by omega)) (by positivity) hU
      _ = (N:ℝ)*U*‖w‖^2 := by simp [mul_assoc]
      _ ≤ ((N+1:ℕ):ℝ)*U*‖w‖^2 := by push_cast; nlinarith [mul_nonneg hU (sq_nonneg ‖w‖)]

/-- The first-order approximation remainder is uniform on every original
Hs ball for 1 <= N <= s, with no extra derivative bound. -/
theorem exists_uniform_nlsRiccatiApproximation_first_order_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ w : ℂ, ‖w‖ ≤ 1 → ∀ x : ℝ,
        ‖nlsRiccatiApproximation a b N w x+b x*w‖ ≤ C*‖w‖^2 := by
  have hprev (k : Fin N) := exists_uniform_nlsRiccatiDensity_pointwise_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  choose U₀ hU₀ hu using hprev
  let U := ∑ k : Fin N, U₀ k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hU₀ k)
  refine ⟨(N:ℝ)*U,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb w hw x
  apply norm_nlsRiccatiApproximation_first_order_le a b N hN U hU _ w hw x
  intro j hj y
  exact (hu ⟨j,hj⟩ ab hab a b ha hb hpa hpb hca hcb y).trans
    (Finset.single_le_sum (fun k _ => hU₀ k) (Finset.mem_univ (⟨j,hj⟩ : Fin N)))

end NLS.ZakharovShabat
