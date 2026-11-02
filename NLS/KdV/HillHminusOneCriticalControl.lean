import NLS.KdV.HillHminusOnePeriodEntries
import NLS.ZakharovShabat.UniformSmallCriticalDisplacements

/-! # Uniform localization of all selected rough Hill critical energies -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusAllContourPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne}
variable (D : HillHminusAllContourPeriodData C N V)
include D

theorem mono {U : Set PeriodOneHminusOne} (hUV : U ⊆ V) (hU : IsOpen U) (h0U : 0 ∈ U) :
    HillHminusAllContourPeriodData C N U where
  isOpen := hU
  zero_mem := h0U
  chart_domain := hUV.trans D.chart_domain
  critical_free := D.critical_free
  critical_analytic n := (D.critical_analytic n).mono hUV
  critical_zero n q hq := D.critical_zero n q (hUV hq)
  critical_simple n q hq := D.critical_simple n q (hUV hq)
  numerator_analytic n := (D.numerator_analytic n).mono (fun _ ht => ⟨ht.1,hUV ht.2⟩)
  numerator_free := D.numerator_free
  numerator_factor n q hq := D.numerator_factor n q (hUV hq)
  numerator_center_ne_zero n q hq := D.numerator_center_ne_zero n q (hUV hq)
  cover k q hq := D.cover k q (hUV hq)
  period_analytic n k := (D.period_analytic n k).mono hUV
  period_free := D.period_free

/-- One rough-open neighborhood controls the unshifted physical square
root of every selected critical energy, including the finite head. -/
theorem exists_uniform_critical_control :
    ∃ U : Set PeriodOneHminusOne, U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ n : ℕ+, ∀ q ∈ U,
        ‖sqrt (hillHminusUniformCriticalPoint C N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 := by
  let phi : PeriodOneHminusOne → PairSpace 2 := fun q => periodOnePotential (C.criticalSource q)
  have hphi : AnalyticOnNhd ℂ phi V := by
    intro q hq
    exact ((periodOnePotential (p := 2)).analyticAt _).comp
      (C.analyticOnNhd_criticalSource q (D.chart_domain hq))
  obtain ⟨Nd,_,W,hW,_,h0W,_,hsmall⟩ := exists_uniform_small_canonicalCriticalDisplacements
    (by simp) (by norm_num) (phi 0) (by positivity : 0 < Real.pi/16)
  obtain ⟨Ns,_,hshift⟩ := exists_high_disc_sqrt_shift_small (-C.energyShift)
    (Real.pi/4) (Real.pi/16) (by positivity)
  let L := max (max N Nd) Ns
  have hfixed (n : ℕ+) : ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ‖sqrt (hillHminusUniformCriticalPoint C N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 := by
    have hs : AnalyticAt ℂ sqrt (hillHminusUniformCriticalPoint C N n 0) := by
      rw [D.critical_free]
      exact Complex.differentiableOn_sqrt.analyticAt
        (Complex.isOpen_slitPlane.mem_nhds (freeHillEnergy_mem_slitPlane n))
    have hc := ((hs.comp (D.critical_analytic n 0 D.zero_mem)).sub
      (analyticAt_const (v := (Real.pi : ℂ)*(n : ℕ)))).continuousAt.norm
    have hz : sqrt (hillHminusUniformCriticalPoint C N n 0)-(Real.pi : ℂ)*(n : ℕ) = 0 := by
      rw [D.critical_free,sqrt_freeHillEnergy]
      ring
    have he : ∀ᶠ q in 𝓝 (0 : PeriodOneHminusOne),
        ‖sqrt (hillHminusUniformCriticalPoint C N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 :=
      hc.eventually (gt_mem_nhds (by
        change ‖sqrt (hillHminusUniformCriticalPoint C N n 0)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8
        rw [hz,norm_zero]
        positivity))
    obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp he
    exact ⟨U,hU,h0U,fun q hq => hUsub hq⟩
  let U (n : ℕ+) := (hfixed n).choose
  have hU (n : ℕ+) := (hfixed n).choose_spec
  let A : Fin (L+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then U ⟨i.val,hi⟩ else univ
  have hA (i : Fin (L+1)) : IsOpen (A i) ∧ (0 : PeriodOneHminusOne) ∈ A i := by
    by_cases hi : 0 < i.val
    · simpa only [A,dif_pos hi] using ⟨(hU ⟨i.val,hi⟩).1,(hU ⟨i.val,hi⟩).2.1⟩
    · simp only [A,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let T := (V ∩ phi ⁻¹' W) ∩ ⋂ i, A i
  refine ⟨T,fun _ hq => hq.1.1,
    (hphi.continuousOn.isOpen_inter_preimage D.isOpen hW).inter
      (isOpen_iInter_of_finite fun i => (hA i).1),
    ⟨⟨D.zero_mem,h0W⟩,mem_iInter.mpr (fun i => (hA i).2)⟩,?_⟩
  intro n q hq
  by_cases hn : (n : ℕ) ≤ L
  · have hi := mem_iInter.mp hq.2 (⟨(n : ℕ),Nat.lt_succ_of_le hn⟩ : Fin (L+1))
    exact (hU n).2.2 q (by simpa only [A,dif_pos n.pos] using! hi)
  have hnN : N < (n : ℕ) := (le_max_left N Nd |>.trans (le_max_left _ _)).trans_lt (Nat.lt_of_not_ge hn)
  have hnD : Nd < (n : ℤ).natAbs := by
    simpa using (le_max_right N Nd |>.trans (le_max_left _ _)).trans_lt (Nat.lt_of_not_ge hn)
  have hnS : Ns ≤ (n : ℕ) := (le_max_right _ _).trans (Nat.lt_of_not_ge hn).le
  have hdelta : ‖C.frequencyCritical q n-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/16 := by
    simpa only [canonicalCriticalDisplacement_apply,HillHminusMiuraChart.frequencyCritical,phi,Int.cast_natCast] using!
      hsmall (phi q) hq.1.2 (periodOnePotential_mem _) (n : ℤ) hnD
  have hball : C.frequencyCritical q n ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
    mem_closedBall_iff_norm.mpr (hdelta.le.trans (by linarith [Real.pi_pos]))
  have hs := (hshift (n : ℕ) hnS _ hball).2
  rw [hillHminusUniformCriticalPoint,if_neg (Nat.not_le_of_gt hnN),HillHminusMiuraChart.energyCritical]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (sqrt ((C.frequencyCritical q n)^2-C.energyShift)) (C.frequencyCritical q n) ((Real.pi : ℂ)*(n : ℕ))
  simp only [sub_eq_add_neg] at hs ht hdelta ⊢
  linarith

end HillHminusAllContourPeriodData
end NLS.KdV
