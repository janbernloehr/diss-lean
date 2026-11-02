import NLS.KdV.ClassicalUniformCriticalBasis
import NLS.KdV.ClassicalCriticalTailAnalytic
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot

/-! # Uniform localization of every selected critical frequency

A finite head and the actual small analytic displacement tail put every
selected critical frequency strictly inside half of the fixed contour
radius on one complex potential neighborhood.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_classicalHill_uniform_critical_frequency_control :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ), 0 < N ∧ IsOpen V ∧ 0 ∈ V ∧
      ∀ n : ℕ+, classicalHillUniformCriticalPoint N n 0 = freeHillEnergy n ∧
        AnalyticOnNhd ℂ (classicalHillUniformCriticalPoint N n) V ∧
        ∀ q ∈ V,
          deriv (classicalHillDiscriminant q) (classicalHillUniformCriticalPoint N n q) = 0 ∧
          deriv (deriv (classicalHillDiscriminant q)) (classicalHillUniformCriticalPoint N n q) ≠ 0 ∧
          ‖Complex.sqrt (classicalHillUniformCriticalPoint N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 := by
  obtain ⟨N,W,hN,hW,h0W,hcrit,_⟩ := exists_classicalHill_uniform_critical_family
  obtain ⟨L,T,_,hT,h0T,_,htail⟩ :=
    exists_small_analytic_classicalHillCriticalFrequencyTail (Real.pi/8) (by positivity)
  have hsmall (n : ℕ+) : ∃ U : Set (NLS.LinearVolterra.Curve ℂ), IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ‖Complex.sqrt (classicalHillUniformCriticalPoint N n q)-
        (Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 := by
    have hs : AnalyticAt ℂ Complex.sqrt (classicalHillUniformCriticalPoint N n 0) := by
      rw [(hcrit n).1]
      exact Complex.differentiableOn_sqrt.analyticAt
        (Complex.isOpen_slitPlane.mem_nhds (freeHillEnergy_mem_slitPlane n))
    have hc : AnalyticAt ℂ (fun q : NLS.LinearVolterra.Curve ℂ =>
        Complex.sqrt (classicalHillUniformCriticalPoint N n q)-(Real.pi : ℂ)*(n : ℕ)) 0 :=
      (hs.comp ((hcrit n).2.1 0 h0W)).sub analyticAt_const
    have hzero : Complex.sqrt (classicalHillUniformCriticalPoint N n 0)-
        (Real.pi : ℂ)*(n : ℕ) = 0 := by
      rw [(hcrit n).1,sqrt_freeHillEnergy]
      ring
    have he : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ),
        ‖Complex.sqrt (classicalHillUniformCriticalPoint N n q)-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 :=
      hc.continuousAt.norm.eventually (gt_mem_nhds (by
        change ‖Complex.sqrt (classicalHillUniformCriticalPoint N n 0)-
          (Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8
        rw [hzero,norm_zero]
        positivity))
    obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp he
    exact ⟨U,hU,h0U,fun q hq => hUsub hq⟩
  let U (n : ℕ+) := Classical.choose (hsmall n)
  have hU (n : ℕ+) := Classical.choose_spec (hsmall n)
  let A : Fin (max N L+1) → Set (NLS.LinearVolterra.Curve ℂ) := fun i =>
    if hi : 0 < i.val then U ⟨i.val,hi⟩ else univ
  have hA (i : Fin (max N L+1)) : IsOpen (A i) ∧ (0 : NLS.LinearVolterra.Curve ℂ) ∈ A i := by
    by_cases hi : 0 < i.val
    · simpa only [A,dif_pos hi] using ⟨(hU ⟨i.val,hi⟩).1,(hU ⟨i.val,hi⟩).2.1⟩
    · simp only [A,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let V := (W ∩ T) ∩ ⋂ i, A i
  refine ⟨N,V,hN,(hW.inter hT).inter (isOpen_iInter_of_finite fun i => (hA i).1),
    ⟨⟨h0W,h0T⟩,mem_iInter.mpr (fun i => (hA i).2)⟩,?_⟩
  intro n
  refine ⟨(hcrit n).1,(hcrit n).2.1.mono (fun _ hq => hq.1.1),?_⟩
  intro q hq
  refine ⟨((hcrit n).2.2 q hq.1.1).1,((hcrit n).2.2 q hq.1.1).2,?_⟩
  by_cases hn : (n : ℕ) ≤ max N L
  · have hi := mem_iInter.mp hq.2 (⟨(n : ℕ),Nat.lt_succ_of_le hn⟩ : Fin (max N L+1))
    exact (hU n).2.2 q (by simpa only [A,dif_pos n.pos] using! hi)
  have hnN : N < (n : ℕ) := (le_max_left N L).trans_lt (Nat.lt_of_not_ge hn)
  have hnL : (L : ℤ) < (n : ℤ) := by
    exact_mod_cast (le_max_right N L).trans_lt (Nat.lt_of_not_ge hn)
  have hcoord := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (classicalHillCriticalFrequencyTail L q) (n : ℤ)
  rw [classicalHillCriticalFrequencyTail_apply,if_pos hnL] at hcoord
  have hdisp : ‖classicalHillFrequencyCritical q n-(Real.pi : ℂ)*(n : ℕ)‖ < Real.pi/8 := by
    simpa only [classicalHillFrequencyCritical,Int.cast_natCast] using!
      hcoord.trans_lt (htail q hq.1.2)
  have hball : classicalHillFrequencyCritical q n ∈
      closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
    apply mem_closedBall_iff_norm.mpr
    exact hdisp.le.trans (by linarith [Real.pi_pos])
  rw [classicalHillUniformCriticalPoint,if_neg (Nat.not_le_of_gt hnN),classicalHillHighCriticalPoint,
    sqrt_sq_of_re_pos _ (re_pos_of_high_closedBall _ n.property _ hball)]
  exact hdisp

end NLS.KdV
