import NLS.ZakharovShabat.SobolevWKBNextForcingL2
import NLS.ZakharovShabat.SobolevWKBLeadingOscillatoryComparison

/-! # The actual next forcing and its free oscillatory response

The next scalar forcing has a uniform L1 bound and its actual response differs from the explicit free term by order N+2.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The explicit next free-oscillatory scalar forcing. -/
def nlsWKBNextScalar (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  ((2*I*z)⁻¹)^(N+1)*nlsWKBNextForcingDensity a b N x*exp (-I*z*x)

theorem continuous_nlsWKBNextScalar (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (z : ℂ) :
    Continuous (nlsWKBNextScalar a b N z) := by
  have hρ := continuous_nlsWKBNextForcingDensity a b ha hb N
  unfold nlsWKBNextScalar
  fun_prop

/-- The free response to the explicit next forcing. -/
def nlsWKBNextFreeTerm (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  ((2*I*z)⁻¹)^(N+1)*exp (I*z*t)*
    (∫ x in (0:ℝ)..t, nlsWKBNextForcingDensity a b N x*exp (-2*I*z*x))

theorem free_integral_nlsWKBNextScalar (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) :
    exp (I*z*t)*(∫ x in (0:ℝ)..t, exp (-I*z*x)*nlsWKBNextScalar a b N z x) =
      nlsWKBNextFreeTerm a b N z t := by
  have he (x : ℝ) : exp (-I*z*x)*nlsWKBNextScalar a b N z x =
      ((2*I*z)⁻¹)^(N+1)*(nlsWKBNextForcingDensity a b N x*exp (-2*I*z*x)) := by
    rw [show -2*I*z*(x:ℂ) = -I*z*x+(-I*z*x) by ring,exp_add]
    unfold nlsWKBNextScalar
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,nlsWKBNextFreeTerm]
  ring

/-- The next scalar forcing has an order-(N+1) L1 bound uniform on the
original Hs ball, including the full truncation order. -/
theorem exists_uniform_nlsWKBNextScalar_integral_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, |z.im| ≤ H →
        (∫ x in (0:ℝ)..1, ‖nlsWKBNextScalar a b N z x‖) ≤ K*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨K,hK,hL2⟩ := exists_uniform_nlsWKBNextForcingDensity_L2_bound s N hs hNs R hR
  refine ⟨K*Real.exp H,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzH
  let ρ := nlsWKBNextForcingDensity a b N
  let w := (2*I*z)⁻¹
  have hρ : Continuous ρ := continuous_nlsWKBNextForcingDensity a b ha hb N
  have hiρ : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ K := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ‖w‖^(N+1)*‖ρ x‖*Real.exp H := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_nlsWKBNextScalar a b ha hb N z).norm.intervalIntegrable 0 1)
        ((continuous_const.mul hρ.norm |>.mul continuous_const).intervalIntegrable 0 1)
      intro x hx
      simp only [nlsWKBNextScalar,norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_exp_neg_I_mul_strip_le z H hzH x hx) (by positivity)
    _ = ‖w‖^(N+1)*(∫ x in (0:ℝ)..1, ‖ρ x‖)*Real.exp H := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul]
    _ ≤ ‖w‖^(N+1)*K*Real.exp H := by gcongr
    _ = _ := by ring

/-- Replacing the actual next-forcing response by its explicit free
oscillatory term leaves an order-(N+2) vector error, uniformly on original
Hs balls and the physical period. -/
theorem exists_uniform_nlsWKB_next_scalar_free_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBNextScalar a b N z)
              (continuous_nlsWKBNextScalar a b ha hb N z)) z t-
          (0,nlsWKBNextFreeTerm a b N z t)‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨K,hK,hint⟩ := exists_uniform_nlsWKBNextScalar_integral_bound s N hs hNs R hR H
  obtain ⟨A,hA,haB⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  let B := Real.exp (A+H)
  let E := 2*classicalSobolevErrorConstant (2*R) H
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hE : 0 ≤ E := mul_nonneg (by norm_num) (classicalSobolevErrorConstant_nonneg _ _ (by positivity))
  refine ⟨3*B*E*K,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let w := (2*I*z)⁻¹
  let f := nlsWKBNextScalar a b N z
  have hf : Continuous f := continuous_nlsWKBNextScalar a b ha hb N z
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    apply norm_prod_le_iff.mpr
    exact ⟨haB ab hab a b ha hb hpa hpb hca hcb x,
      haB (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  have hsol (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (x : Icc (0:ℝ) 1) : ‖classicalSolution Φ z v x‖ ≤ B :=
    norm_classicalSolution_unit_strip_le A H Φ hΦ z hzH v hv x
  have herr (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (x : Icc (0:ℝ) 1) :
      ‖classicalSolution Φ z v x-classicalFreeVector z v x‖ ≤ E*‖w‖ := by
    have hh := norm_classicalSolution_sub_free_higherSobolev_le s hs R H ab hab a b
      ha.continuous hb.continuous hpa hpb hca hcb z (norm_pos_iff.mp (by linarith)) hzH v x
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hE hv) (norm_nonneg _)
  have hfree (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖exp (-I*z*x)‖ ≤ B :=
    (norm_exp_neg_I_mul_strip_le z H hzH x hx).trans (Real.exp_le_exp.mpr (by linarith))
  have hh := norm_classicalScalarForcing_sub_free_le Φ z f hf B (E*‖w‖) hB (by positivity)
    hsol herr hfree t
  rw [free_integral_nlsWKBNextScalar] at hh
  apply hh.trans
  calc
    _ ≤ 3*B*(E*‖w‖)*(K*‖w‖^(N+1)) :=
      mul_le_mul_of_nonneg_left (hint ab hab a b ha hb hpa hpb hca hcb z hzH) (by positivity)
    _ = (3*B*E*K)*‖w‖^(N+2) := by rw [show N+2=(N+1)+1 by omega,pow_succ]; ring

end NLS.ZakharovShabat
