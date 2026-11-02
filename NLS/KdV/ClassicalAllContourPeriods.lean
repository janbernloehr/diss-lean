import NLS.KdV.ClassicalUniformCriticalLocalization
import NLS.KdV.ClassicalUniformPrimitiveBounds
import NLS.KdV.ClassicalPeriodIntegrationByParts

/-! # One all-mode contour family for the actual period operator

Every positive mode uses the quadratic image of C(k*pi,pi/4). All source,
critical and numerator data are constructed on the same neighborhood.
This removes finite-head contour changes from the operator estimates.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- Simultaneous actual spectral controls for one selected numerator
family. Existence below supplies every field, including all low modes. -/
structure ClassicalAllContourPeriodData (N : ℕ)
    (V : Set (NLS.LinearVolterra.Curve ℂ)) (A : ℝ) : Prop where
  isOpen : IsOpen V
  zero_mem : 0 ∈ V
  amplitude_pos : 0 < A
  critical_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformCriticalPoint N n) V
  critical_free : ∀ n : ℕ+, classicalHillUniformCriticalPoint N n 0 = freeHillEnergy n
  critical_zero : ∀ n : ℕ+, ∀ q ∈ V,
    deriv (classicalHillDiscriminant q) (classicalHillUniformCriticalPoint N n q) = 0
  critical_simple : ∀ n : ℕ+, ∀ q ∈ V,
    deriv (deriv (classicalHillDiscriminant q)) (classicalHillUniformCriticalPoint N n q) ≠ 0
  critical_close : ∀ n : ℕ+, ∀ q ∈ V,
    ‖Complex.sqrt (classicalHillUniformCriticalPoint N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8
  numerator_analytic : ∀ n : ℕ+,
    AnalyticOnNhd ℂ (classicalHillUniformNumerator N n) (univ ×ˢ V)
  numerator_free : ∀ n : ℕ+, ∀ z : ℂ,
    classicalHillUniformNumerator N n (z,0) = classicalHillFreePsi n z
  numerator_factor : ∀ n : ℕ+, ∀ q ∈ V, ∀ z : ℂ,
    (z-classicalHillUniformCriticalPoint N n q)*classicalHillUniformNumerator N n (z,q) =
      (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) z
  cover : ∀ k : ℕ+, ∀ q ∈ V,
    ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      (z^2,q) ∈ classicalHillContinuationDomain
  primitive_bound : ∀ k : ℕ+, ∀ q ∈ V,
    ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      ‖classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi‖ ≤ A
  period_analytic : ∀ n k : ℕ+, AnalyticOnNhd ℂ (classicalHillUniformHighPeriod N n k) V
  period_free : ∀ n k : ℕ+, classicalHillUniformHighPeriod N n k 0 = if n = k then 1 else 0

theorem ClassicalAllContourPeriodData.mono {N : ℕ} {A : ℝ}
    {V U : Set (NLS.LinearVolterra.Curve ℂ)} (D : ClassicalAllContourPeriodData N V A)
    (hsub : U ⊆ V) (hU : IsOpen U) (h0U : 0 ∈ U) : ClassicalAllContourPeriodData N U A where
  isOpen := hU
  zero_mem := h0U
  amplitude_pos := D.amplitude_pos
  critical_analytic n := (D.critical_analytic n).mono hsub
  critical_free := D.critical_free
  critical_zero n q hq := D.critical_zero n q (hsub hq)
  critical_simple n q hq := D.critical_simple n q (hsub hq)
  critical_close n q hq := D.critical_close n q (hsub hq)
  numerator_analytic n := (D.numerator_analytic n).mono (fun _ ht => ⟨ht.1,hsub ht.2⟩)
  numerator_free := D.numerator_free
  numerator_factor n q hq := D.numerator_factor n q (hsub hq)
  cover k q hq := D.cover k q (hsub hq)
  primitive_bound k q hq := D.primitive_bound k q (hsub hq)
  period_analytic n k := (D.period_analytic n k).mono hsub
  period_free := D.period_free

theorem exists_classicalHill_all_contour_period_data :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), ∃ A : ℝ,
      0 < N ∧ ClassicalAllContourPeriodData N V A := by
  obtain ⟨N,W,hN,hW,h0W,hcrit⟩ := exists_classicalHill_uniform_critical_frequency_control
  obtain ⟨R,C,hR,_,hC,hprim⟩ := exists_classicalHill_uniform_contour_primitive_bounds
  let V := W ∩ ball (0 : NLS.LinearVolterra.Curve ℂ) R
  have hV : IsOpen V := hW.inter isOpen_ball
  have h0V : (0 : NLS.LinearVolterra.Curve ℂ) ∈ V := ⟨h0W,mem_ball_self hR⟩
  have hμ (n : ℕ+) : AnalyticOnNhd ℂ (classicalHillUniformCriticalPoint N n) V :=
    (hcrit n).2.1.mono inter_subset_left
  have hF : AnalyticOnNhd ℂ classicalHillDiscriminantDerivative (univ ×ˢ V) :=
    analyticOnNhd_classicalHillDiscriminantDerivative.mono (subset_univ _)
  have hB (n : ℕ+) : AnalyticOnNhd ℂ (classicalHillUniformNumerator N n) (univ ×ˢ V) :=
    analyticOnNhd_const.mul (analyticOnNhd_parametricMovingDividedDifference _ _ hV hF (hμ n))
  have hfree (n : ℕ+) (z : ℂ) :
      classicalHillUniformNumerator N n (z,0) = classicalHillFreePsi n z := by
    rw [classicalHillUniformNumerator,
      parametricMovingDividedDifference_eq_dslope _ _ hF (hμ n) z 0 h0V,(hcrit n).1]
    rfl
  have hcover (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
      (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      (z^2,q) ∈ classicalHillContinuationDomain :=
    (hprim q (by simpa only [mem_ball,dist_zero_right] using hq.2) k z hz).1
  refine ⟨N,V,Real.pi/4+C*R,hN,{
    isOpen := hV
    zero_mem := h0V
    amplitude_pos := by positivity
    critical_analytic := hμ
    critical_free := fun n => (hcrit n).1
    critical_zero := fun n q hq => ((hcrit n).2.2 q hq.1).1
    critical_simple := fun n q hq => ((hcrit n).2.2 q hq.1).2.1
    critical_close := fun n q hq => ((hcrit n).2.2 q hq.1).2.2
    numerator_analytic := hB
    numerator_free := hfree
    numerator_factor := ?_
    cover := hcover
    primitive_bound := ?_
    period_analytic := ?_
    period_free := ?_ }⟩
  · intro n q hq z
    have he := parametricMovingDividedDifference_mul _ _ hF (hμ n) z q hq
    change (z-classicalHillUniformCriticalPoint N n q)*
      parametricMovingDividedDifference _ _ (z,q) =
        deriv (classicalHillDiscriminant q) z-
          deriv (classicalHillDiscriminant q) (classicalHillUniformCriticalPoint N n q) at he
    rw [((hcrit n).2.2 q hq.1).1,sub_zero] at he
    dsimp only [classicalHillUniformNumerator]
    linear_combination (2*(n : ℂ)*Real.pi)*he
  · intro k q hq z hz
    have hqR : ‖q‖ < R := by simpa only [mem_ball,dist_zero_right] using hq.2
    exact (hprim q hqR k z hz).2.2.2.trans (by nlinarith)
  · intro n k
    let D := classicalHillContinuationDomain ∩ (univ ×ˢ V)
    have hD : IsOpen D := isOpen_classicalHillContinuationDomain.inter (isOpen_univ.prod hV)
    have hI : AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
        classicalHillUniformNumerator N n t/classicalHillContinuedRoot t) D := by
      apply ((hB n).mono inter_subset_right).div
        (analyticOnNhd_classicalHillContinuedRoot.mono inter_subset_left)
      intro t ht
      exact classicalHillContinuedRoot_ne_zero t ht.1
    let T : ℂ × NLS.LinearVolterra.Curve ℂ → ℂ × NLS.LinearVolterra.Curve ℂ :=
      fun t => (t.1^2,t.2)
    have hT : Continuous T := by fun_prop
    have hG : AnalyticOnNhd ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ =>
        (classicalHillUniformNumerator N n (t.1^2,t.2)/
          classicalHillContinuedRoot (t.1^2,t.2))*(2*t.1)) (T ⁻¹' D) := by
      intro t ht
      exact ((hI (T t) ht).comp
        (f := T) ((analyticAt_fst.pow 2).prod analyticAt_snd)).mul
          (analyticAt_const.mul analyticAt_fst)
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic _ (hD.preimage hT) hG
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) (by positivity) hV
      (fun q hq z hz => ⟨hcover k q hq z hz,mem_univ _,hq⟩)
    exact analyticOnNhd_const.mul hi
  intro n k
  unfold classicalHillUniformHighPeriod
  simp only [hfree,classicalHillContinuedRoot_base,circleIntegral_classicalHillFreePsi_frequency]
  split_ifs
  · exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
  · exact mul_zero _

end NLS.KdV
