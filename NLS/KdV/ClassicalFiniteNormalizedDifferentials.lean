import NLS.KdV.ClassicalCriticalPeriods
import NLS.ComplexAnalysis.AnalyticFinitePeriodNormalization

/-! # Actual finite families of normalized Hill differentials

For any finite set of distinct positive modes, construct entire numerators
jointly analytic near the free potential and normalize their periods on all
selected contours simultaneously. This solves the actual finite equations;
it does not assert normalization on the unselected infinitely many gaps.
-/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.KdV
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_classicalHill_finite_normalized_differentials (e : ι ↪ ℕ+) :
    ∃ V : Set (NLS.LinearVolterra.Curve ℂ), IsOpen V ∧ 0 ∈ V ∧
      ∃ Ψ : ι → ℂ × NLS.LinearVolterra.Curve ℂ → ℂ,
        (∀ n, AnalyticOnNhd ℂ (Ψ n) (univ ×ˢ V)) ∧
        (∀ n z, Ψ n (z,0) = classicalHillFreePsi (e n) z) ∧
        (∀ q ∈ V, ∀ k, ∀ z ∈ sphere (freeHillEnergy (e k)) (classicalHillFreeFrequencyRadius (e k)),
          (z,q) ∈ classicalHillContinuationDomain) ∧
        ∀ q ∈ V, ∀ n k,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C(freeHillEnergy (e k),classicalHillFreeFrequencyRadius (e k)),
            Ψ n (z,q)/classicalHillContinuedRoot (z,q) = if n = k then 1 else 0 := by
  classical
  let P := fun q j k => classicalHillCriticalPeriod (e j) (e k) q
  have hP (j k : ι) : AnalyticAt ℂ (fun q => P q j k) 0 := by
    obtain ⟨U, _, h0U, _, _, hU⟩ := exists_analytic_classicalHillCriticalPeriod (e j) (e k)
    exact hU 0 h0U
  have hP0 (j k : ι) : P 0 j k = if j = k then 1 else 0 := by
    dsimp only [P]
    rw [classicalHillCriticalPeriod_free]
    by_cases h : j = k
    · subst k
      simp
    · simp only [if_neg h, if_neg (fun he => h (e.injective he))]
  obtain ⟨C, VC, hVC, h0C, hC, hC0, hsolve⟩ :=
    ComplexAnalysis.exists_analytic_finite_period_normalization P 0 hP hP0
  let U := fun j k => Classical.choose (exists_analytic_classicalHillCriticalPeriod (e j) (e k))
  have hU (j k : ι) := Classical.choose_spec (exists_analytic_classicalHillCriticalPeriod (e j) (e k))
  let V := VC ∩ ⋂ j, ⋂ k, U j k
  have hV : IsOpen V := hVC.inter (isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => (hU j k).1)
  have h0V : (0 : NLS.LinearVolterra.Curve ℂ) ∈ V := by
    refine ⟨h0C, mem_iInter.mpr ?_⟩
    intro j
    exact mem_iInter.mpr (fun k => (hU j k).2.1)
  have hVU (j k : ι) : V ⊆ U j k := by
    intro q hq
    exact mem_iInter.mp (mem_iInter.mp hq.2 j) k
  let Ψ := fun n (t : ℂ × NLS.LinearVolterra.Curve ℂ) =>
    ∑ j, C t.2 n j*classicalHillCriticalNumerator (e j) t
  refine ⟨V, hV, h0V, Ψ, ?_, ?_, ?_, ?_⟩
  · intro n
    apply Finset.analyticOnNhd_fun_sum
    intro j _ t ht
    have hc : AnalyticAt ℂ (fun q => C q n j) t.2 :=
      analyticAt_pi_iff.mp (analyticAt_pi_iff.mp (hC t.2 ht.2.1) n) j
    have hcs : AnalyticAt ℂ (fun t : ℂ × NLS.LinearVolterra.Curve ℂ => C t.2 n j) t := by
      simpa only [Function.comp_def] using! hc.comp
        (f := fun t : ℂ × NLS.LinearVolterra.Curve ℂ => t.2) (analyticAt_snd (p := t))
    exact hcs.mul (analyticOnNhd_classicalHillCriticalNumerator (e j) t
      ⟨mem_univ _,(hU j n).2.2.1 (hVU j n ht.2)⟩)
  · intro n z
    dsimp only [Ψ]
    simp only [hC0, classicalHillCriticalNumerator_free]
    simp
  · intro q hq k z hz
    exact (hU k k).2.2.2.1 q (hVU k k hq) z hz
  intro q hq n k
  have hR := (Classical.choose_spec (exists_classicalHillFreePsi_periods (e k))).1
  have hi (j : ι) : CircleIntegrable (fun z =>
      classicalHillCriticalNumerator (e j) (z,q)/classicalHillContinuedRoot (z,q))
      (freeHillEnergy (e k)) (classicalHillFreeFrequencyRadius (e k)) := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hqu := hVU j k hq
    have hdom := (hU j k).2.2.2.1 q hqu z hz
    have hn := (analyticOnNhd_classicalHillCriticalNumerator (e j) (z,q)
      ⟨mem_univ _,(hU j k).2.2.1 hqu⟩).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
    have hr := (analyticOnNhd_classicalHillContinuedRoot (z,q) hdom).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
    exact (hn.div hr (classicalHillContinuedRoot_ne_zero (z,q) hdom)).continuousAt.continuousWithinAt
  have heq : (2*(Real.pi : ℂ))⁻¹ * ∮ z in
      C(freeHillEnergy (e k),classicalHillFreeFrequencyRadius (e k)),
      Ψ n (z,q)/classicalHillContinuedRoot (z,q) = ∑ j, C q n j*P q j k := by
    calc
      _ = (2*(Real.pi : ℂ))⁻¹ * ∮ z in
          C(freeHillEnergy (e k),classicalHillFreeFrequencyRadius (e k)),
          ∑ j, C q n j*(classicalHillCriticalNumerator (e j) (z,q)/classicalHillContinuedRoot (z,q)) := by
        congr 1
        apply circleIntegral.integral_congr hR.le
        intro z _
        change (∑ j, C q n j*classicalHillCriticalNumerator (e j) (z,q))/
          classicalHillContinuedRoot (z,q) = _
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = (2*(Real.pi : ℂ))⁻¹ * ∑ j, C q n j *
          (∮ z in C(freeHillEnergy (e k),classicalHillFreeFrequencyRadius (e k)),
            classicalHillCriticalNumerator (e j) (z,q)/classicalHillContinuedRoot (z,q)) := by
        have hci (j : ι) : CircleIntegrable (fun z => C q n j*
            (classicalHillCriticalNumerator (e j) (z,q)/classicalHillContinuedRoot (z,q)))
            (freeHillEnergy (e k)) (classicalHillFreeFrequencyRadius (e k)) := by
          simpa only [Pi.smul_apply, smul_eq_mul] using! (hi j).const_smul (a := C q n j)
        rw [circleIntegral.integral_fun_sum (fun j _ => hci j)]
        simp only [circleIntegral.integral_const_mul]
      _ = ∑ j, C q n j*P q j k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [P, classicalHillCriticalPeriod]
        ring
  exact heq.trans (hsolve q hq.1 n k)

end NLS.KdV
