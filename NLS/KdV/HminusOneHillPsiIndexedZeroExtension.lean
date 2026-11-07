import NLS.KdV.HminusOneHillPsiRealZeroContinuity
import NLS.KdV.HminusOneHillPsiZeroBranches
import NLS.ComplexAnalysis.SimpleRootSelectionUniqueness

/-! A local complex analytic continuation agrees with the ACTUAL
indexed real zero coefficient at EVERY nearby real source. The proof
uses continuity of the indexed real selection and simple-root local
uniqueness, rather than only matching its value at one source.
The neighborhood is still allowed to depend on both indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_local_analytic_indexed_hillHminusPsi_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n m : ℕ+) (hmn : m ≠ n) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusCanonicalPsiDomain ∧
      ∃ s : PeriodOneHminusOne → ℂ, AnalyticOnNhd ℂ s U ∧
        (∀ a ∈ U, ∀ ha : IsRealPeriodOneHminusOne a,
          s a = (hillHminusCanonicalPsiRealZero n m a ha:ℂ)) ∧
        ∀ a ∈ U, hillHminusCanonicalPsi n (s a,a) = 0 ∧
          deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,a)) (s a) ≠ 0 := by
  obtain ⟨V,hV,hqV,hVD,s,hs,hsq,hroots⟩ :=
    exists_local_analytic_hillHminusCanonicalPsi_retained_zero q hr n m hmn
  let x : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} := ⟨q,hr⟩
  let g : {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a} → ℂ := fun a =>
    (hillHminusCanonicalPsiRealZero n m a.val a.property:ℂ)
  have hg : ContinuousAt g x :=
    Complex.continuous_ofReal.continuousAt.comp
      (f := fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} =>
        hillHminusCanonicalPsiRealZero n m a.val a.property)
      (continuousAt_hillHminusCanonicalPsiRealZero n m x)
  have hsc : ContinuousAt (fun a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} => s a.val) x :=
    (hs q hqV).continuousAt.comp (f := Subtype.val) continuous_subtype_val.continuousAt
  have hF := analyticOnNhd_hillHminusCanonicalPsi n (g x,q)
    ⟨mem_univ _,real_mem_hillHminusCanonicalPsiDomain q hr⟩
  have hz : hillHminusCanonicalPsi n (g x,q) = 0 :=
    hillHminusCanonicalPsiRealZero_is_zero n m q hr hmn
  have hd : (fderiv ℂ (hillHminusCanonicalPsi n) (g x,q)) (1,0) ≠ 0 := by
    rw [← deriv_spectral_section_eq_fderiv (hillHminusCanonicalPsi n) (g x) q hF.differentiableAt]
    exact hillHminusCanonicalPsi_deriv_ne_zero_of_real_source q hr n (g x) hz
  have hnear : ∀ᶠ a : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b} in 𝓝 x, a.val ∈ V :=
    continuous_subtype_val.continuousAt.eventually (hV.mem_nhds hqV)
  have hmatch : g =ᶠ[𝓝 x] (fun a => s a.val) := by
    apply eventually_eq_of_continuous_simple_root_selections (hillHminusCanonicalPsi n)
      Subtype.val g (fun a => s a.val) x hF continuous_subtype_val.continuousAt hg hsc hsq.symm _ _ hd
    · exact Eventually.of_forall (fun a => hillHminusCanonicalPsiRealZero_is_zero n m a.val a.property hmn)
    · filter_upwards [hnear] with a ha
      exact (hroots a.val ha).1
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp hmatch
  refine ⟨V ∩ ball q r,hV.inter isOpen_ball,⟨hqV,mem_ball_self hrpos⟩,
    (fun a ha => hVD ha.1),s,hs.mono inter_subset_left,?_,?_⟩
  · intro a ha har
    have hmem : (⟨a,har⟩ : {b : PeriodOneHminusOne // IsRealPeriodOneHminusOne b}) ∈ ball x r := by
      change dist a q < r
      exact mem_ball.mp ha.2
    exact (hball hmem).symm
  · exact fun a ha => hroots a ha.1

end NLS.KdV
