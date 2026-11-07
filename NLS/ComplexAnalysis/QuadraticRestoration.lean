import NLS.ComplexAnalysis.QuadraticLiftUniqueness
import NLS.ComplexAnalysis.AnalyticScalarFactorUniqueness

/-! Restoring one energy factor in the exact quadratic differential
lift cannot annihilate a nonzero entire energy coefficient. The zero
frequency and restored energy are included by analytic cancellation. -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem quadratic_restoration_ne_zero (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ)
    (hPne : P ≠ 0) (b c : ℂ) :
    (fun z : ℂ => (b-(z^2-c))*(2*z*P (z^2-c))) ≠ 0 := by
  intro hzero
  let R : ℂ → ℂ := fun E => (b-E)*P E
  have hR : AnalyticOnNhd ℂ R univ := (analyticOnNhd_const.sub analyticOnNhd_id).mul hP
  have hRzero : R = 0 := by
    apply eq_of_quadratic_differential_pullback_eq R (fun _ => 0)
      (continuousOn_univ.mp hR.continuousOn) continuous_const c
    intro z
    simp only [mul_zero]
    calc
      2*z*R (z^2-c) = (b-(z^2-c))*(2*z*P (z^2-c)) := by dsimp only [R]; ring
      _ = 0 := congrFun hzero z
  have hnontrivial : ∃ E ∈ (univ : Set ℂ), (b-E) ≠ 0 := by
    refine ⟨b+1,mem_univ _,?_⟩
    intro he
    have h : (1:ℂ) = 0 := by linear_combination -he
    exact one_ne_zero h
  have hPzero : EqOn P (fun _ => (0:ℂ)) univ :=
    analytic_eqOn_of_mul_eq_mul_on_open isPreconnected_univ isOpen_univ Subset.rfl
      (fun E : ℂ => b-E) P (fun _ => 0)
      (analyticOnNhd_const.sub analyticOnNhd_id) hP analyticOnNhd_const hnontrivial (by
        intro E _
        have h := congrFun hRzero E
        simpa only [R,Pi.zero_apply,mul_zero] using h)
  exact hPne (funext (fun E => hPzero (mem_univ E)))

end NLS.ComplexAnalysis
