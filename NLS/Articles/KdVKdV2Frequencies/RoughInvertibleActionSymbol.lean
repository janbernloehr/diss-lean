import NLS.Articles.KdVKdV2Frequencies.RoughActionAmplitudeBounds
import NLS.SequenceSpaces.PositiveAnalyticReciprocal

/-! # Actual action amplitude symbols with native positive reciprocals -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE complex rough ball before all positive modes supports the actual
normalized action amplitude, its exact reciprocal and uniform bounds. -/
theorem exists_hillHminus_action_symbol_reciprocal :
    ∃ η C : ℝ, ∃ M N : PeriodOneHminusOne → Coeff ⊤,
      0<η ∧ 0<C ∧ AnalyticOnNhd ℂ M (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ N (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖M q‖≤C ∧ ‖N q‖≤8 ∧
        (∀ j : ℤ, j≤0 → M q j=0 ∧ N q j=0) ∧ ∀ n : ℕ+,
          (1/8 : ℝ)≤‖M q (n : ℤ)‖ ∧ N q (n : ℤ)=(M q (n : ℤ))⁻¹ ∧ M q (n : ℤ)*N q (n : ℤ)=1) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
          M (hillPhysicalHminusEmbedding p).val (n : ℤ)=
            (Real.sqrt (1+(n : ℝ)) : ℂ)*hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨η,C,A,hη,hC,hAa,hAb,hAp⟩ := exists_hillHminus_native_action_amplitude_symbol_bounds
  obtain ⟨M,hMa,hMd⟩ := Coeff.exists_positive_bounded_analytic_lift (ball (0 : PeriodOneHminusOne) η) isOpen_ball
    (fun n q => A q (n : ℤ)) C hC.le (by
      intro n q hq
      exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ (n : ℤ)).analyticAt (A q)).comp (hAa q hq))
    (fun q hq n => (hAb q hq n).2)
  have hl (q : PeriodOneHminusOne) (hq : q∈ball (0 : PeriodOneHminusOne) η) (n : ℕ+) :
      (1/8 : ℝ)≤‖M q (n : ℤ)‖ := by rw [(hMd q hq).2.2];exact (hAb q hq n).1
  obtain ⟨N,hNa,hNd⟩ := Coeff.exists_positive_analytic_reciprocal (ball (0 : PeriodOneHminusOne) η) isOpen_ball
    M hMa (1/8) (by norm_num) hl
  refine ⟨η,C,M,N,hη,hC,hMa,hNa,?_,?_⟩
  · intro q hq
    refine ⟨(hMd q hq).1,by simpa using (hNd q hq).1,
      fun j hj => ⟨(hMd q hq).2.1 j hj,(hNd q hq).2.1 j hj⟩,fun n => ⟨hl q hq n,(hNd q hq).2.2 n⟩⟩
  · intro p hp n
    rw [(hMd _ hp).2.2]
    exact hAp p hp n

end NLS.Articles.KdVKdV2Frequencies
