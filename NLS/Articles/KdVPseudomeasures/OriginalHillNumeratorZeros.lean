import NLS.Articles.KdVPseudomeasures.OriginalHillEnergyDifferentials
import NLS.KdV.HminusOneHillPsiFixedShift
import NLS.KdV.HminusOneHillPsiRealZeros

/-! Actual retained-gap zeros and sub-sine pullback growth for the local
original Hill numerators. These are inputs toward the original product
representation; a product, unique zeros, squared-gap bounds, and
independence under changes of physical energy shift are not asserted. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_local_Hill_numerator_gap_zeros :
    ∃ A : MiuraHillPsiFamily, ∀ q : OriginalHminusOnePotential,
      ∃ B : HillHminusDirichletBall, originalPeriodOneCoefficients q ∈ B.psiSource A ∧
        IsOpen (B.psiSource A) ∧ B.psiSource A ⊆ hillHminusCanonicalDirichletDomain ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (B.psiNumerator A n) (univ ×ˢ B.psiSource A) ∧
          AnalyticOnNhd ℂ (B.energyDifferential A n) (B.energyDomain A)) ∧
        (∀ n m : ℕ+, m ≠ n → ∃ E : ℝ,
          E ∈ Icc (originalHillLabels q (2*(m:ℕ)-1)) (originalHillLabels q (2*(m:ℕ))) ∧
          B.psiNumerator A n ((E:ℂ),originalPeriodOneCoefficients q) = 0) ∧
        ∀ n : ℕ+, ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
          ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k),
            ‖(2*z*B.psiNumerator A n (z^2-(B.miuraBall.actionBall.shift:ℂ),
              originalPeriodOneCoefficients q))/(-2*sin z)‖ ≤ ε := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  refine ⟨A,?_⟩
  intro q
  obtain ⟨B,hB⟩ := exists_local_hminusHillPsiFamily A _ (originalPeriodOneCoefficients_real q)
  refine ⟨B,hB,B.psiSource_open A,B.psiSource_subset_dirichletDomain A,?_,?_,?_⟩
  · exact fun n => ⟨B.analytic_psiNumerator A n,B.analytic_energyDifferential A n⟩
  · exact fun n m hmn => B.exists_psiNumerator_zero_in_original_gap A _ hB
      (originalPeriodOneCoefficients_real q) n m hmn
  · intro n ε hε
    simpa only [HillHminusDirichletBall.psiNumerator,sub_add_cancel] using
      A.numerator_pullback_sub_sine_growth n (B.miuraBall.actionBall.lift (originalPeriodOneCoefficients q)) ε hε

/-- The common complex agreement neighborhood precedes EVERY index and energy. -/
theorem original_local_Hill_numerators_agree_at_same_shift
    (A D : MiuraHillPsiFamily) (B C : HillHminusDirichletBall)
    (hc : B.miuraBall.actionBall.shift = C.miuraBall.actionBall.shift)
    (q : OriginalHminusOnePotential)
    (hB : originalPeriodOneCoefficients q ∈ B.psiSource A)
    (hC : originalPeriodOneCoefficients q ∈ C.psiSource D) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ originalPeriodOneCoefficients q ∈ U ∧
      U ⊆ B.psiSource A ∩ C.psiSource D ∧ ∀ n : ℕ+, ∀ E : ℂ,
        EqOn (fun a => B.psiNumerator A n (E,a)) (fun a => C.psiNumerator D n (E,a)) U :=
  B.exists_complex_same_shift_numerator_agreement C A D hc _
    (originalPeriodOneCoefficients_real q) hB hC

end NLS.Articles.KdVPseudomeasures
