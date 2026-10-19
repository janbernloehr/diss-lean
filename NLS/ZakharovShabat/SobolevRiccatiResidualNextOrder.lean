import NLS.ZakharovShabat.NLSRiccatiResidualNextOrder
import NLS.ZakharovShabat.SobolevRiccatiResidualCorrectionUniform

/-! # Uniform next-order Riccati residual bounds

The next residual density and the improved residual error have uniform bounds on original Sobolev balls through the full truncation order.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The next residual density is continuous for smooth potentials. -/
theorem continuous_nlsRiccatiResidualNextDensity (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    Continuous (nlsRiccatiResidualNextDensity a b N) :=
  continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N (N+1)

/-- The explicit next residual coefficient and the error after removing
it have common bounds on the original Hs ball. No extra source derivative
is used, including at the full order N=s. -/
theorem exists_uniform_nlsRiccatiResidual_next_order_bounds
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) → ∀ x : ℝ,
        ‖nlsRiccatiResidualNextDensity a b N x‖ ≤ C ∧
        ∀ w : ℂ, ‖w‖ ≤ 1 →
          ‖(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w+
            nlsRiccatiDensity a b N x*w^N-nlsRiccatiResidualNextDensity a b N x*w^(N+1)‖ ≤
              C*‖w‖^(N+2) := by
  obtain ⟨A,hA,ha⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  have hprev (k : Fin N) := exists_uniform_nlsRiccatiDensity_pointwise_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  choose U₀ hU₀ hu using hprev
  let U := ∑ k : Fin N, U₀ k
  let D := ∑ k ∈ Finset.range (2*N+3), A*(k+1)*U^2
  let B := A*((N:ℝ)+2)*U^2
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hU₀ k)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => by positivity)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B+D,add_nonneg hB hD,?_⟩
  intro ab hab a b hca hcb hpa hpb hfa hfb x
  have hρ (j : ℕ) (hj : j < N) (y : ℝ) : ‖nlsRiccatiDensity a b j y‖ ≤ U :=
    (hu ⟨j,hj⟩ ab hab a b hca hcb hpa hpb hfa hfb y).trans
      (Finset.single_le_sum (fun k _ => hU₀ k) (Finset.mem_univ (⟨j,hj⟩ : Fin N)))
  have hn : ‖nlsRiccatiResidualNextDensity a b N x‖ ≤ B := by
    have hh := norm_coeff_nlsRiccatiResidualPolynomial_above_le a b N (N+1) (by omega)
      A U hA hU (ha ab hab a b hca hcb hpa hpb hfa hfb) hρ x
    simpa only [nlsRiccatiResidualNextDensity,B,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1:ℝ)+1=2 by norm_num] using hh
  refine ⟨hn.trans (le_add_of_nonneg_right hD),?_⟩
  intro w hw
  exact (norm_nlsRiccatiResidual_next_order_le a b N A U hA hU
    (ha ab hab a b hca hcb hpa hpb hfa hfb) hρ x w hw).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (by positivity))

end NLS.ZakharovShabat
