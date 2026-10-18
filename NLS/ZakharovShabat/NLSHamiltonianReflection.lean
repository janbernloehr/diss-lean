import NLS.ZakharovShabat.NLSHamiltonianReflectedPhaseEstimate
import NLS.ComplexAnalysis.SampledAnalyticOrder

/-! # Reflection parity of the physical NLS Hamiltonians

Analytic order recovers the exact Hamiltonian parity identity from the sampled phase estimates.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Each original physical Hamiltonian has the exact signed-reflection
coefficient relation, recovered from the actual discriminant asymptotics. -/
theorem classicalNLSHamiltonian_reflection_relation
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (k : ℕ) :
    classicalNLSHamiltonian a b (k+1)+(-1:ℂ)^(k+1)*classicalNLSHamiltonian (-b) (-a) (k+1) = 0 := by
  let r : ℕ → ℝ := fun j => Real.pi*((j:ℝ)+1/2)
  have hr : Tendsto r atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop Real.pi_pos
  have hcos (j : ℕ) : Real.cos (r j) = 0 := by
    have h : r j = (j:ℝ)*Real.pi+Real.pi/2 := by dsimp [r]; ring
    rw [h,Real.cos_add_pi_div_two,Real.sin_nat_mul_pi,neg_zero]
  have hw : Tendsto (fun j => (r j:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Pi.inv_apply,ofReal_inv,ofReal_zero] using!
      (continuous_ofReal.tendsto 0).comp hr.inv_tendsto_atTop
  have hw0 : ∀ᶠ j in atTop, (r j:ℂ)⁻¹ ≠ 0 := by
    filter_upwards [hr.eventually (eventually_gt_atTop 0)] with j hj
    exact inv_ne_zero (ofReal_ne_zero.mpr hj.ne')
  let P := nlsHamiltonianCorrection a b (k+2)
  let Q := nlsHamiltonianCorrection (-b) (-a) (k+2)
  have hP : AnalyticAt ℂ P 0 := analyticAt_nlsHamiltonianCorrection a b (k+2) 0
  have hQ : AnalyticAt ℂ (fun w => Q (-w)) 0 := by
    have h := (analyticAt_nlsHamiltonianCorrection (-b) (-a) (k+2) (-(0:ℂ))).comp
      (f := fun w : ℂ => -w) analyticAt_id.neg
    simpa only [Q,Function.comp_def] using! h
  obtain ⟨C,_,hbound⟩ := exists_nlsHamiltonian_reflected_phase_sampled_bound a b ha hb hpa hpb
    r hr hcos (k+2)
  have hzero := iteratedDeriv_eq_zero_of_sampled_bound (fun w => P w+Q (-w)) (hP.add hQ)
    (fun j => (r j:ℂ)⁻¹) hw hw0 (k+2) C hbound (k+1) (by omega)
  rw [iteratedDeriv_fun_add hP.contDiffAt hQ.contDiffAt,iteratedDeriv_comp_neg,neg_zero,smul_eq_mul] at hzero
  dsimp only [P,Q] at hzero
  rw [iteratedDeriv_nlsHamiltonianCorrection a b (k+2) k (by omega),
    iteratedDeriv_nlsHamiltonianCorrection (-b) (-a) (k+2) k (by omega)] at hzero
  have he : (((k+1).factorial:ℂ)*I/2^(k+1))*
      (classicalNLSHamiltonian a b (k+1)+(-1:ℂ)^(k+1)*classicalNLSHamiltonian (-b) (-a) (k+1)) = 0 := by
    linear_combination hzero
  exact (mul_eq_zero.mp he).resolve_left (by
    apply div_ne_zero
    · exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (k+1)) I_ne_zero
    · exact pow_ne_zero _ (by norm_num))

/-- The signed potential swap multiplies the kth positive Hamiltonian
by its exact parity sign. -/
theorem classicalNLSHamiltonian_signedSwap
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (k : ℕ) :
    classicalNLSHamiltonian (-b) (-a) (k+1) = (-1:ℂ)^k*classicalNLSHamiltonian a b (k+1) := by
  have h := classicalNLSHamiltonian_reflection_relation a b ha hb hpa hpb k
  rw [pow_succ,mul_neg_one] at h
  have he : (-1:ℂ)^k*(-1:ℂ)^k = 1 := by rw [← mul_pow]; norm_num
  linear_combination -(-1:ℂ)^k*h-classicalNLSHamiltonian (-b) (-a) (k+1)*he

end NLS.ZakharovShabat
