import NLS.ZakharovShabat.SobolevRiccatiApproximationUniform
import NLS.ZakharovShabat.NLSRiccatiResidualDegree
import NLS.ZakharovShabat.NLSRiccatiResidualIntegralCoefficient
import NLS.ComplexAnalysis.PolynomialFunctionIntegralPower

/-! # Uniform integrated Riccati residuals

For N <= s the order-N residual bound is uniform on the original Hs ball. The proof uses no additional source derivative.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The full Riccati residual has an integrated order-N bound uniform on
an original Hs ball for N <= s, without requiring any additional derivative. -/
theorem exists_uniform_nlsRiccatiResidual_integral_bound (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ f g : ℝ → ℂ,
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) →
      ∀ w : ℂ, ‖w‖ ≤ 1 →
        (∫ x in (0:ℝ)..1, ‖(nlsRiccatiResidualPolynomial f g N).eval₂
          (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w‖) ≤ C*‖w‖^N := by
  obtain ⟨A,hA,ha⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  have hprev (k : Fin N) := exists_uniform_nlsRiccatiDensity_pointwise_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  have hdprev (k : Fin N) := exists_uniform_deriv_nlsRiccatiDensity_L2_bound
    s k.val (lt_of_lt_of_le k.isLt hNs) R hR
  choose U₀ hU₀ hu using hprev
  choose D₀ hD₀ hd using hdprev
  let U := ∑ k : Fin N, U₀ k
  let D := ∑ k : Fin N, D₀ k
  have hU : 0 ≤ U := Finset.sum_nonneg (fun k _ => hU₀ k)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => hD₀ k)
  let C (k : ℕ) := U+A+D+A*(k+1)*U^2
  refine ⟨∑ k ∈ Finset.range (2*N+3), C k,Finset.sum_nonneg (fun k _ => by dsimp only [C]; positivity),?_⟩
  intro ab hab f g hf hg hpf hpg hca hcb w hw
  have haf (x : ℝ) : ‖f x‖ ≤ A := ha ab hab f g hf hg hpf hpg hca hcb x
  have hag (x : ℝ) : ‖g x‖ ≤ A :=
    ha (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
      g f hg hf hpg hpf hcb hca x
  have hρ (j : ℕ) (hj : j < N) (x : ℝ) : ‖nlsRiccatiDensity f g j x‖ ≤ U := by
    apply (hu ⟨j,hj⟩ ab hab f g hf hg hpf hpg hca hcb x).trans
    exact Finset.single_le_sum (fun k _ => hU₀ k) (Finset.mem_univ (⟨j,hj⟩ : Fin N))
  have hρd (j : ℕ) (hj : j < N) :
      (∫ x in (0:ℝ)..1, ‖deriv (nlsRiccatiDensity f g j) x‖) ≤ D := by
    have hcont := (contDiff_infty_iff_deriv.mp (contDiff_nlsRiccatiDensity f g hf hg j)).2.continuous
    have hi := integral_norm_le_sqrt_length_mul_L2 (deriv (nlsRiccatiDensity f g j)) 1
      (by norm_num) (memLp_two_interval hcont 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    apply hi.trans ((hd ⟨j,hj⟩ ab hab f g hf hg hpf hpg hca hcb).trans _)
    exact Finset.single_le_sum (fun k _ => hD₀ k) (Finset.mem_univ (⟨j,hj⟩ : Fin N))
  apply integral_polynomial_function_power_le _
    (continuous_coeff_nlsRiccatiResidualPolynomial f g hf hg N) N (2*N+3)
    (by have hh := natDegree_nlsRiccatiResidualPolynomial_le f g N; omega)
    (X_pow_dvd_nlsRiccatiResidualPolynomial f g N) C _ w hw
  intro k _
  exact integral_norm_nlsRiccatiResidualPolynomial_coeff_le f g hf hg N k
    A A U D hA hA hU hD haf hag hρ hρd

end NLS.ZakharovShabat
