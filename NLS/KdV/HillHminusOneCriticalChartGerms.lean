import NLS.KdV.HillHminusOneCriticalChartIndependence
import NLS.ComplexAnalysis.SimpleRootGermUniqueness

/-! # Compatible complex germs of actual rough Hill critical charts

At every real overlap, the canonical energy labels agree on a full complex
neighborhood for each index. Nearby complex inputs need not be real type.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV.HillHminusMiuraChart

theorem eventually_energyCritical_is_critical (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) :
    ∀ᶠ p in 𝓝 q, deriv (hillHminusDiscriminant p) (C.energyCritical p j) = 0 := by
  have ha := (analyticAt_sourceCanonicalCriticalPoint_of_realType (by simp) (by norm_num)
    (j:ℤ) (C.criticalSource q) hr).comp (f := C.criticalSource) (C.analyticOnNhd_criticalSource q hq)
  have hn : C.frequencyCritical q j ≠ 0 := by
    intro he
    have hp := (C.frequencyCritical_pos_real q hr j).1
    rw [he,zero_re] at hp
    exact (lt_irrefl _ hp)
  have hc : ContinuousAt (fun p => C.frequencyCritical p j) q := ha.continuousAt
  filter_upwards [hc.eventually_ne hn,C.domain_open.mem_nhds hq] with p hp hpC
  have hz := canonicalCriticalPoints_is_critical (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource p)) (periodOnePotential_mem _) (j:ℤ)
  change deriv (canonicalDiscriminant (by simp) (periodOnePotential (C.criticalSource p)))
    (C.frequencyCritical p j) = 0 at hz
  rw [C.frequency_derivative_eq p hpC] at hz
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hp)

/-- A continuous actual critical branch with the correct value has the
same full complex germ as the canonical branch at every real input. -/
theorem eventuallyEq_energyCritical_of_simple_root (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+)
    (b : PeriodOneHminusOne → ℂ) (hb : ContinuousAt b q)
    (he : b q = C.energyCritical q j)
    (hz : ∀ᶠ p in 𝓝 q, deriv (hillHminusDiscriminant p) (b p) = 0) :
    b =ᶠ[𝓝 q] (fun p => C.energyCritical p j) := by
  obtain ⟨r,hrpos,han⟩ := (C.analyticAt_energyCritical_of_realType q hr hq j).exists_ball_analyticOnNhd
  exact eventuallyEq_of_simple_spectral_root hillHminusDiscriminantDerivative
    (fun p => C.energyCritical p j) b Metric.isOpen_ball
    (analyticOnNhd_hillHminusDiscriminantDerivative.mono (subset_univ _)) han q
    (Metric.mem_ball_self hrpos) hb he (C.energyCritical_simple q hr hq j)
    (C.eventually_energyCritical_is_critical q hq hr j) hz

/-- Every pair of real-preserving actual charts has matching complex germs
at each real overlap. The neighborhood may depend on the positive index. -/
theorem eventuallyEq_energyCritical_of_real_overlap (C D : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.domain) (hqD : q ∈ D.domain)
    (hrC : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hrD : IsRealType (CoeffPair.toMax 2 (D.criticalSource q)))
    (hc : C.energyShift.im = 0) (hd : D.energyShift.im = 0) (j : ℕ+) :
    (fun p => D.energyCritical p j) =ᶠ[𝓝 q] (fun p => C.energyCritical p j) := by
  exact C.eventuallyEq_energyCritical_of_simple_root q hqC hrC j _
    (D.analyticAt_energyCritical_of_realType q hrD hqD j).continuousAt
    (C.energyCritical_eq_of_real_overlap D q hqC hqD hrC hrD hc hd j).symm
    (D.eventually_energyCritical_is_critical q hqD hrD j)

end NLS.KdV.HillHminusMiuraChart
