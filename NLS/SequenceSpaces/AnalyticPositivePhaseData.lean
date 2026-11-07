import NLS.SequenceSpaces.PositiveBoundedAnalyticFamily
import NLS.ComplexAnalysis.SharpExponentialRemainder

/-! One inverse-index analytic scalar phase family gives both its actual
inverse phase and bounded analytic weighted error on a common domain. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem exists_positive_analytic_phase_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (R : ℕ+ → E → ℂ)
    (hRa : ∀ n,AnalyticOnNhd ℂ (R n) U) (K : ℝ) (hK : 0≤K)
    (hb : ∀ p∈U,∀ n : ℕ+,(1+(n:ℝ))*‖R n p‖≤K) :
    ∃ N M : E → Coeff ⊤,AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ M U ∧ ∀ p∈U,
      ‖N p‖≤Real.exp K ∧ ‖M p‖≤K*Real.exp K ∧
      (∀ j : ℤ,j≤0 → N p j=0 ∧ M p j=0) ∧ ∀ n : ℕ+,
        N p (n:ℤ)=exp (-I*R n p) ∧ M p (n:ℤ)=(1+(n:ℂ))*(exp (I*R n p)-1) ∧
        exp (I*R n p)*N p (n:ℤ)=1 := by
  have hRb (p) (hp : p∈U) (n : ℕ+) : ‖R n p‖≤K := by
    have h := hb p hp n
    nlinarith [norm_nonneg (R n p),show (0:ℝ)≤n by positivity]
  have hNbound (p) (hp : p∈U) (n : ℕ+) : ‖exp (-I*R n p)‖≤Real.exp K :=
    (norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by simpa only [norm_mul,norm_neg,norm_I,one_mul] using hRb p hp n))
  have hMbound (p) (hp : p∈U) (n : ℕ+) : ‖(1+(n:ℂ))*(exp (I*R n p)-1)‖≤K*Real.exp K := by
    have he := NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp (I*R n p)
    simp only [norm_mul,norm_I,one_mul] at he
    have he' := he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hRb p hp n)) (norm_nonneg _))
    rw [norm_mul,show ‖1+(n:ℂ)‖=1+(n:ℝ) by
      rw [←Nat.cast_one,←Nat.cast_add,Complex.norm_natCast,Nat.cast_add,Nat.cast_one]]
    calc
      _ ≤ (1+(n:ℝ))*(‖R n p‖*Real.exp K) := mul_le_mul_of_nonneg_left he' (by positivity)
      _ = ((1+(n:ℝ))*‖R n p‖)*Real.exp K := by ring
      _ ≤ K*Real.exp K := mul_le_mul_of_nonneg_right (hb p hp n) (Real.exp_pos K).le
  obtain ⟨N,hNa,hN⟩ := exists_positive_bounded_analytic_lift U hU (fun n p => exp (-I*R n p)) (Real.exp K)
    (Real.exp_pos K).le (fun n p hp => (analyticAt_const.mul (hRa n p hp)).cexp') hNbound
  obtain ⟨M,hMa,hM⟩ := exists_positive_bounded_analytic_lift U hU
    (fun n p => (1+(n:ℂ))*(exp (I*R n p)-1)) (K*Real.exp K) (by positivity)
    (fun n p hp => analyticAt_const.mul ((analyticAt_const.mul (hRa n p hp)).cexp'.sub analyticAt_const)) hMbound
  refine ⟨N,M,hNa,hMa,?_⟩
  intro p hp
  refine ⟨(hN p hp).1,(hM p hp).1,(fun j hj => ⟨(hN p hp).2.1 j hj,(hM p hp).2.1 j hj⟩),?_⟩
  intro n
  refine ⟨(hN p hp).2.2 n,(hM p hp).2.2 n,?_⟩
  rw [(hN p hp).2.2 n,←exp_add,show I*R n p+-I*R n p=0 by ring,exp_zero]

end NLS.Coeff
