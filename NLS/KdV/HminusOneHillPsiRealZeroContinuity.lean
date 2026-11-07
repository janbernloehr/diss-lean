import NLS.KdV.HminusOneCanonicalHillPsiRealZero
import NLS.KdV.HillOriginalPositiveEndpointContinuity
import NLS.RealAnalysis.ContinuousIntervalZero

/-! The ACTUAL indexed real Hill zero coefficients are continuous on
the full native H-minus-one real form. The unique retained zero lies
in a continuously moving original compact gap; its omitted coefficient
is the continuous original midpoint. Collapsed gaps require no exception. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.RealAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem continuousAt_hillHminusCanonicalPsiRealZero (n m : ℕ+)
    (q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a}) :
    ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
      hillHminusCanonicalPsiRealZero n m a.val a.property) q := by
  obtain ⟨hl,hr⟩ := continuousAt_hillHminusPositiveGapEndpoints m q
  by_cases hmn : m = n
  · have he : (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
        hillHminusCanonicalPsiRealZero n m a.val a.property) =
        (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
          (hillHminusLabels a.val a.property (2*(m:ℕ)-1)+hillHminusLabels a.val a.property (2*(m:ℕ)))/2) := by
      funext a
      rw [hillHminusCanonicalPsiRealZero,dif_pos hmn]
    rw [he]
    exact (hl.add hr).div_const 2
  · apply continuousAt_unique_zero_in_interval
      (fun t : ℝ × {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
        hillHminusCanonicalPsi n ((t.1:ℂ),t.2.val))
      (fun a => hillHminusLabels a.val a.property (2*(m:ℕ)-1))
      (fun a => hillHminusLabels a.val a.property (2*(m:ℕ))) _ q hl hr
    · intro E
      have hQ : Continuous (fun t : ℝ × {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
          ((t.1:ℂ),t.2.val)) :=
        (Complex.continuous_ofReal.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
      exact (analyticOnNhd_hillHminusCanonicalPsi n ((E:ℂ),q.val)
        ⟨mem_univ _,real_mem_hillHminusCanonicalPsiDomain q.val q.property⟩).continuousAt.comp (x := (E,q))
          (f := fun t : ℝ × {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} => ((t.1:ℂ),t.2.val)) hQ.continuousAt
    · intro a
      exact hillHminusCanonicalPsiRealZero_mem_gap n m a.val a.property
    · intro a
      exact hillHminusCanonicalPsiRealZero_is_zero n m a.val a.property hmn
    · intro E hE hz
      exact hillHminusCanonicalPsiRealZero_unique n m q.val q.property hmn E hE hz

theorem continuous_hillHminusCanonicalPsiRealZero (n m : ℕ+) :
    Continuous (fun q : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} =>
      hillHminusCanonicalPsiRealZero n m q.val q.property) :=
  continuous_iff_continuousAt.mpr (continuousAt_hillHminusCanonicalPsiRealZero n m)

end NLS.KdV
