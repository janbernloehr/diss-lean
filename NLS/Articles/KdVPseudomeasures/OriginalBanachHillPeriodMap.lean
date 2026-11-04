import NLS.Articles.KdVPseudomeasures.OriginalHillFrequencyCoordinates
import NLS.KdV.HillProductEquationDerivative

/-! The FULL original weighted Hill period map is jointly Banach
analytic near every physical real H-minus-one potential, on one OPEN
placed-input domain BEFORE ALL n. Genuine common contours and exact
midpoint rows are retained. This prerequisite does not assert the
nonzero-source Jacobian inverse or analytic actual zero sequence. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_common_Banach_Hill_period_map (q₀ : OriginalHminusOnePotential) :
    ∃ P : HillProductEquationPatch, originalPeriodOneCoefficients q₀ ∈ P.source ∧
      P.parent.center = originalPeriodOneCoefficients q₀ ∧ IsOpen P.inputDomain ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (P.equation n) P.inputDomain ∧
        AnalyticOnNhd ℂ (P.sequenceJacobian n) P.inputDomain) ∧
      (∀ t ∈ P.inputDomain,
        ∃ J : Set (lp (fun _ : ℕ+ => ℂ) 2 × PeriodOneHminusOne),
          IsOpen J ∧ t ∈ J ∧ J ⊆ P.inputDomain ∧
          ∃ L : ℝ, 0 ≤ L ∧ ∀ n : ℕ+, ∀ s ∈ J, ‖P.equation n s‖ ≤ L) ∧
      (∀ n m : ℕ+, ∀ t ∈ P.inputDomain,
        P.equation n t m = P.parent.productEquationRow n m
          (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) t) ∧
      ∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ P.source → ∀ n : ℕ+,
        (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) ∈ P.inputDomain ∧
        P.equation n (originalHillPsiZeroDisplacement n q,originalPeriodOneCoefficients q) = 0 := by
  obtain ⟨P,hq,hcenter⟩ := exists_hillProductEquationPatch (originalPeriodOneCoefficients q₀)
    (originalPeriodOneCoefficients_real q₀)
  refine ⟨P,hq,hcenter,P.inputDomain_open,
    (fun n => ⟨P.analytic_equation n,P.analytic_sequenceJacobian n⟩),
    P.exists_local_uniform_equation_bound,?_,?_⟩
  · intro n m t ht
    exact (P.equation_apply n m t ht).trans (P.row_eq_native n m t)
  · intro q hq n
    exact ⟨P.actual_real_graph_mem _ hq (originalPeriodOneCoefficients_real q) n,
      P.equation_actual_real_zeros n _ hq (originalPeriodOneCoefficients_real q)⟩

end NLS.Articles.KdVPseudomeasures
