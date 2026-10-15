import NLS.Fourier.SmoothPeriodicDistribution
import NLS.Fourier.PolynomialPeriodicDistribution

/-! # Theorem A.1 on the original smooth periodic test space

Finite order gives polynomial coefficient growth of the same degree. Every
polynomially growing sequence gives a unique original periodic distribution.
The least order, physical exponentials, and exact period scaling are retained.
-/
noncomputable section
open Set Filter Topology
open scoped SchwartzMap ContDiff BoundedContinuousFunction
namespace NLS.Fourier

/-- A global bracket bound implies the literal cofinite asymptotic, including degree zero. -/
theorem polynomial_isBigO_of_bracket_bound (α : ℤ → ℂ) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℤ, ‖α n‖ ≤ C*(1+|(n:ℝ)|)^N) :
    Asymptotics.IsBigO cofinite α (fun n : ℤ => |(n:ℝ)|^N) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C*2^N,?_⟩
  filter_upwards [(Filter.le_cofinite_iff_eventually_ne.mp le_rfl) (0:ℤ)] with n hn
  have hn' : n ≠ 0 := by simpa using hn
  have hnat : 1 ≤ |n| := Int.one_le_abs hn'
  have hreal : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast hnat
  have hp : (1+|(n:ℝ)|)^N ≤ (2*|(n:ℝ)|)^N := pow_le_pow_left₀ (by positivity) (by linarith) N
  calc
    _ ≤ C*(1+|(n:ℝ)|)^N := hb n
    _ ≤ C*(2*|(n:ℝ)|)^N := mul_le_mul_of_nonneg_left hp hC
    _ = (C*2^N)*‖|(n:ℝ)|^N‖ := by rw [Real.norm_of_nonneg (by positivity),mul_pow]; ring

namespace SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

theorem norm_derivative_mode_apply (n : ℤ) (k : ℕ) (x : ℝ) :
    ‖derivative (Fact.out : 0 < L).ne' k (mode n : SmoothPeriodicTest L) x‖ =
      (|(L/2)⁻¹| *Real.pi*|(n:ℝ)|)^k := by
  change ‖iteratedDeriv k (fun x => wave n ((L/2)⁻¹*x)) x‖ = _
  rw [iteratedDeriv_comp_const_smul (contDiff_infty.mp (contDiff_wave_infty n) k),norm_smul,
    norm_pow,Real.norm_eq_abs,iteratedDeriv_wave,norm_mul,norm_pow]
  have hw : ‖wave n ((L/2)⁻¹*x)‖ = 1 := by simp [wave,Complex.norm_exp]
  rw [hw,mul_one]
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
  simp only [mul_pow]
  ring

theorem norm_derivative_mode (n : ℤ) (k : ℕ) :
    ‖derivative (Fact.out : 0 < L).ne' k (mode n : SmoothPeriodicTest L)‖ =
      (|(L/2)⁻¹| *Real.pi*|(n:ℝ)|)^k := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun x => (norm_derivative_mode_apply n k x).le)
  · simpa only [norm_derivative_mode_apply] using
      BoundedContinuousFunction.norm_coe_le_norm (derivative (Fact.out : 0 < L).ne' k (mode n : SmoothPeriodicTest L)) 0

theorem cNorm_mode_bound (N : ℕ) (n : ℤ) :
    cNorm (Fact.out : 0 < L).ne' N (mode n : SmoothPeriodicTest L) ≤
      (N+1)*(1+|(L/2)⁻¹| *Real.pi)^N*(1+|(n:ℝ)|)^N := by
  rw [cNorm_apply]
  have hd : 0 ≤ |(L/2)⁻¹| *Real.pi := by positivity
  have hdn : 0 ≤ |(L/2)⁻¹| *Real.pi*|(n:ℝ)| := by positivity
  calc
    _ ≤ ∑ j ∈ Finset.range (N+1), ((1+|(L/2)⁻¹| *Real.pi)*(1+|(n:ℝ)|))^N := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_derivative_mode]
      apply (pow_le_pow_left₀ (by positivity) ?_ j).trans
        (pow_le_pow_right₀ (by nlinarith [abs_nonneg (n:ℝ)] : 1 ≤ (1+|(L/2)⁻¹| *Real.pi)*(1+|(n:ℝ)|)) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      nlinarith [abs_nonneg (n:ℝ)]
    _ = _ := by simp [mul_pow]; ring

namespace Distribution

def HasOrderAtMost (u : Distribution L) (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f, ‖u f‖ ≤ C*cNorm (Fact.out : 0 < L).ne' N f

theorem exists_order (u : Distribution L) : ∃ N, u.HasOrderAtMost N :=
  (continuous_iff_finite_order u.toLinearMap).mp u.continuous

/-- The least N in the original finite-order estimate (A.1). -/
def order (u : Distribution L) : ℕ := by classical exact Nat.find u.exists_order

theorem hasOrderAtMost_order (u : Distribution L) : u.HasOrderAtMost u.order := by classical exact Nat.find_spec u.exists_order

theorem order_le {u : Distribution L} {N : ℕ} (h : u.HasOrderAtMost N) : u.order ≤ N := by classical exact Nat.find_min' u.exists_order h

/-- Part (i) of Theorem A.1 with the prescribed order, not an enlarged degree. -/
theorem coefficients_isBigO_of_order {u : Distribution L} {N : ℕ} (h : u.HasOrderAtMost N) :
    Asymptotics.IsBigO cofinite (fun n : ℤ => u (mode (-n))) (fun n : ℤ => |(n:ℝ)|^N) := by
  obtain ⟨C,hC,hb⟩ := h
  apply polynomial_isBigO_of_bracket_bound _ N (C*(N+1)*(1+|(L/2)⁻¹| *Real.pi)^N) (by positivity)
  intro n
  have he := (hb (mode (-n))).trans (mul_le_mul_of_nonneg_left (cNorm_mode_bound (L := L) N (-n)) hC.le)
  simpa only [Int.cast_neg,abs_neg,mul_assoc] using he

/-- Literal least-order form of Theorem A.1(i). -/
theorem coefficients_isBigO (u : Distribution L) :
    Asymptotics.IsBigO cofinite (fun n : ℤ => u (mode (-n))) (fun n : ℤ => |(n:ℝ)|^u.order) :=
  coefficients_isBigO_of_order u.hasOrderAtMost_order

/-- Part (ii) of Theorem A.1, uniquely on every original smooth periodic test. -/
theorem existsUnique_of_polynomial_isBigO (α : ℤ → ℂ) (N : ℕ)
    (hα : Asymptotics.IsBigO cofinite α (fun n : ℤ => |(n:ℝ)|^N)) :
    ∃! u : Distribution L, ∀ n : ℤ, u (mode (-n)) = α n := by
  obtain ⟨T,⟨hT,hc⟩,_⟩ := existsUnique_periodicDistribution_of_polynomial_isBigO L Fact.out α N hα
  refine ⟨ofTempered T,fun n => (ofTempered_coefficient T hT n).trans (hc n),?_⟩
  intro v hv
  apply ext_coefficients
  intro n
  rw [hv n,ofTempered_coefficient T hT n,hc n]

/-- Exact characterization on the original periodic test space. -/
theorem polynomial_growth_iff_existsUnique (α : ℤ → ℂ) :
    (∃ N : ℕ, Asymptotics.IsBigO cofinite α (fun n : ℤ => |(n:ℝ)|^N)) ↔
      ∃! u : Distribution L, ∀ n : ℤ, u (mode (-n)) = α n := by
  constructor
  · rintro ⟨N,hN⟩
    exact existsUnique_of_polynomial_isBigO α N hN
  · rintro ⟨u,hc,_⟩
    exact ⟨u.order,by simpa only [hc] using u.coefficients_isBigO⟩

/-- Point evaluation is an order-zero distribution in the original convention. -/
def evaluationLM (x : ℝ) : SmoothPeriodicTest L →ₗ[ℂ] ℂ where
  toFun := fun f => f x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def evaluation (x : ℝ) : Distribution L where
  toLinearMap := evaluationLM x
  cont := by
    apply (continuous_iff_finite_order (evaluationLM x)).mpr
    refine ⟨0,1,by norm_num,fun f => ?_⟩
    change ‖f x‖ ≤ 1*cNorm (Fact.out : 0 < L).ne' 0 f
    simpa only [one_mul,derivative_apply,iteratedDeriv_zero] using
      (BoundedContinuousFunction.norm_coe_le_norm (derivative (Fact.out : 0 < L).ne' 0 f) x).trans
        (derivative_norm_le_cNorm (Fact.out : 0 < L).ne' f (le_refl 0))

theorem evaluation_order (x : ℝ) : (evaluation x : Distribution L).order = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply order_le
  refine ⟨1,by norm_num,fun f => ?_⟩
  change ‖f x‖ ≤ 1*cNorm (Fact.out : 0 < L).ne' 0 f
  simpa only [one_mul,derivative_apply,iteratedDeriv_zero] using
    (BoundedContinuousFunction.norm_coe_le_norm (derivative (Fact.out : 0 < L).ne' 0 f) x).trans
      (derivative_norm_le_cNorm (Fact.out : 0 < L).ne' f (le_refl 0))

theorem evaluation_zero_coefficient (n : ℤ) :
    (evaluation 0 : Distribution L) (mode (-n)) = 1 := by
  change wave (-n) ((L/2)⁻¹*0) = 1
  simp

end Distribution

/-- The derivative normalization agrees with the physical period L. -/
theorem norm_derivative_mode_physical (n : ℤ) (k : ℕ) :
    ‖derivative (Fact.out : 0 < L).ne' k (mode n : SmoothPeriodicTest L)‖ =
      (2*Real.pi*|(n:ℝ)|/L)^k := by
  rw [norm_derivative_mode]
  congr 1
  have hL : 0 < L := Fact.out
  rw [abs_of_pos (by positivity : 0 < (L/2)⁻¹)]
  field_simp

/-- The test exponential has exactly the normalization printed in Appendix A. -/
theorem mode_apply_physical (n : ℤ) (x : ℝ) :
    (mode n : SmoothPeriodicTest L) x = Complex.exp (Complex.I*(2*(n:ℂ)*(Real.pi:ℂ)/(L:ℂ))*x) := by
  change Complex.exp (((Real.pi:ℂ)*Complex.I*n)*(((L/2)⁻¹*x:ℝ):ℂ)) = _
  congr 1
  push_cast
  field_simp

end SmoothPeriodicTest

/-- Theorem A.1 also characterizes the existing actual distribution realization. -/
theorem periodicDistribution_coefficients_isBigO (L : ℝ) (hL : 0 < L)
    (T : 𝓢'(ℝ,ℂ)) (hT : IsPeriodicDistribution L T) :
    ∃ N : ℕ, Asymptotics.IsBigO cofinite (fun n : ℤ => T (periodCoefficientTest L hL n))
      (fun n : ℤ => |(n:ℝ)|^N) := by
  let : Fact (0 < L) := ⟨hL⟩
  let u : SmoothPeriodicTest.Distribution L := SmoothPeriodicTest.Distribution.ofTempered T
  exact ⟨u.order,by simpa only [u,SmoothPeriodicTest.Distribution.ofTempered_coefficient T hT] using u.coefficients_isBigO⟩

end NLS.Fourier
