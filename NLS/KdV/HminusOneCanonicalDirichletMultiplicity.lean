import NLS.KdV.HminusOneCanonicalDirichletSpectrum
import NLS.KdV.HminusOneDirichletLabelAsymptotics
import NLS.ComplexAnalysis.SimpleRootBranchUniqueness

/-! # No collisions and full physical multiplicities of the analytic divisor

If two analytic simple Dirichlet branches collide, local implicit
uniqueness makes their germs equal. Analytic continuation on the common
connected domain would then identify their distinct original free values.
Thus the entire positive sequence is injective at EVERY complex source.
Together with spectral exhaustion this gives exact full native counts.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

theorem hillHminusCanonicalDirichlet_zero (n : ℕ+) :
    hillHminusCanonicalDirichlet n 0 = (((Real.pi*(n : ℝ))^2 : ℝ) : ℂ) := by
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  rw [hillHminusCanonicalDirichlet_eq_real 0 hzero n,hillHminusDirichletLabels_zero hzero n]

theorem injective_hillHminusCanonicalDirichlet (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    Function.Injective (fun n : ℕ+ => hillHminusCanonicalDirichlet n q) := by
  intro n m he
  let F : ℂ × PeriodOneHminusOne → ℂ := fun t => hillHminusDirichlet t.2 t.1
  have hF := analyticOnNhd_hillHminusDirichlet_joint (hillHminusCanonicalDirichlet n q,q) (mem_univ _)
  have hs : (fderiv ℂ F (hillHminusCanonicalDirichlet n q,q)) (1,0) ≠ 0 := by
    rw [← deriv_spectral_section_eq_fderiv F _ q hF.differentiableAt]
    exact deriv_hillHminusCanonicalDirichlet_ne_zero n q hq
  have hlocal := eventually_eq_of_continuous_simple_root_branches F
    (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m) q hF
    (analyticOnNhd_hillHminusCanonicalDirichlet n q hq).continuousAt
    (analyticOnNhd_hillHminusCanonicalDirichlet m q hq).continuousAt he
    (by
      filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds hq] with a ha
      exact hillHminusCanonicalDirichlet_is_root n a ha)
    (by
      filter_upwards [isOpen_hillHminusCanonicalDirichletDomain.mem_nhds hq] with a ha
      exact hillHminusCanonicalDirichlet_is_root m a ha) hs
  have hall := (analyticOnNhd_hillHminusCanonicalDirichlet n).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_hillHminusCanonicalDirichlet m) isConnected_hillHminusCanonicalDirichletDomain.isPreconnected hq hlocal
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hfree := hall (real_mem_hillHminusCanonicalDirichletDomain 0 hzero)
  rw [hillHminusCanonicalDirichlet_zero,hillHminusCanonicalDirichlet_zero] at hfree
  have hsq : (Real.pi*(n : ℝ))^2 = (Real.pi*(m : ℝ))^2 := ofReal_inj.mp hfree
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hp := (sq_eq_sq₀ (mul_nonneg Real.pi_pos.le hn) (mul_nonneg Real.pi_pos.le hm)).mp hsq
  have hcast : (n : ℝ) = (m : ℝ) := mul_left_cancel₀ Real.pi_ne_zero hp
  apply PNat.coe_injective
  exact_mod_cast hcast

theorem hillHminusCanonicalDirichlet_global_multiplicity (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) (energy : ℂ) :
    (∑ᶠ n : ℕ+, if hillHminusCanonicalDirichlet n q = energy then (1 : ℕ) else 0) =
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) energy := by
  have hinj := injective_hillHminusCanonicalDirichlet q hq
  by_cases hz : hillHminusDirichlet q energy = 0
  · obtain ⟨n,hn⟩ := (hillHminusCanonicalDirichlet_roots_iff q hq energy).mp hz
    have hothers (m : ℕ+) (hm : m ≠ n) :
        (if hillHminusCanonicalDirichlet m q = energy then (1 : ℕ) else 0) = 0 := by
      apply if_neg
      intro he
      exact hm (hinj (he.trans hn))
    rw [finsum_eq_single _ n hothers,if_pos hn.symm]
    rw [hn]
    exact (hillHminusCanonicalDirichlet_native_multiplicity n q hq).symm
  · have hterms : (fun n : ℕ+ => if hillHminusCanonicalDirichlet n q = energy then (1 : ℕ) else 0) = 0 := by
      funext n
      apply if_neg
      intro he
      exact hz (he ▸ hillHminusCanonicalDirichlet_is_root n q hq)
    have ho : analyticOrderAt (hillHminusDirichlet q) energy = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hz)
    rw [hterms]
    change (∑ᶠ _ : ℕ+, (0 : ℕ)) = _
    rw [finsum_zero,singularDirichletAlgebraicMultiplicity_eq_analyticOrderNatAt,analyticOrderNatAt,ho]
    rfl

end NLS.KdV
