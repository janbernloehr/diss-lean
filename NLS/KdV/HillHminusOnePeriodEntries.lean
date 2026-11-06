import NLS.KdV.HillHminusOneCriticalNumerators
import NLS.KdV.ClassicalHillLowOddDifferentialMoments
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-! # Actual all-mode Hill period entries on a common Hminus1 neighborhood

Compact source tubes handle the finite head of the original frequency
circles. Their infinite high tail uses the proved rough annulus coverage.
Every entry is analytic on one rough-open neighborhood and the complete
free matrix is the identity. An operator inverse is not assumed here.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.KdV

theorem hillHminusContinuationDomain_zero_of_classical (z : ℂ)
    (hz : (z,(0 : Curve ℂ)) ∈ classicalHillContinuationDomain) :
    (z,(0 : PeriodOneHminusOne)) ∈ hillHminusContinuationDomain := by
  rw [mem_hillHminusContinuationDomain_iff]
  refine ⟨(classicalHillContinuationDomain_subset hz).1,?_⟩
  intro s _
  have hc := (classicalHillContinuationDomain_subset hz).2
  simpa only [smul_zero,hillHminusRadicand,hillHminusDiscriminant_zero,
    classicalHillRadicand,classicalHillDiscriminant_zero] using hc

@[simp] theorem hillHminusContinuedRoot_base (z : ℂ) :
    hillHminusContinuedRoot (z,0) = classicalHillFreeRoot z := by
  change hillHminusSourceFamily.root (z,0) = _
  rw [TracePrimitiveFamily.root_base]
  rfl

theorem exists_hillHminus_fixed_frequency_contour_neighborhood (k : ℕ+) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ 0 ∈ V ∧ ∀ q ∈ V,
      ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
        (z^2,q) ∈ hillHminusContinuationDomain := by
  let S := sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)
  let O : Set (ℂ × PeriodOneHminusOne) :=
    (fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) ⁻¹' hillHminusContinuationDomain
  have hT : Continuous (fun t : ℂ × PeriodOneHminusOne => (t.1^2,t.2)) :=
    (continuous_fst.pow 2).prodMk continuous_snd
  have hO : IsOpen O := isOpen_hillHminusContinuationDomain.preimage hT
  have hs : S ×ˢ {(0 : PeriodOneHminusOne)} ⊆ O := by
    rintro ⟨z,q⟩ ⟨hz,hq⟩
    obtain rfl := mem_singleton_iff.mp hq
    change (z^2,(0 : PeriodOneHminusOne)) ∈ hillHminusContinuationDomain
    exact hillHminusContinuationDomain_zero_of_classical _
      (classicalHill_free_frequency_annulus_coverage k (Real.pi/4) (by positivity) z
        (sphere_subset_closedBall hz) (mem_sphere_iff_norm.mp hz).ge)
  have hS : IsCompact S := isCompact_sphere _ _
  have hzero : IsCompact ({(0 : PeriodOneHminusOne)} : Set PeriodOneHminusOne) := isCompact_singleton
  obtain ⟨W,V,_,hV,hSW,h0,hsub⟩ := generalized_tube_lemma hS hzero hO hs
  refine ⟨V,hV,h0 (mem_singleton _),?_⟩
  intro q hq z hz
  change (z,q) ∈ O
  exact hsub ⟨hSW hz,hq⟩

def hillHminusPeriodEntry (C : HillHminusMiuraChart) (N : ℕ) (n k : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    (hillHminusUniformNumerator C N n (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z)

structure HillHminusAllContourPeriodData (C : HillHminusMiuraChart) (N : ℕ)
    (V : Set PeriodOneHminusOne) : Prop where
  isOpen : IsOpen V
  zero_mem : 0 ∈ V
  chart_domain : V ⊆ C.domain
  critical_free : ∀ n : ℕ+, hillHminusUniformCriticalPoint C N n 0 = freeHillEnergy n
  critical_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusUniformCriticalPoint C N n) V
  critical_zero : ∀ n : ℕ+, ∀ q ∈ V,
    deriv (hillHminusDiscriminant q) (hillHminusUniformCriticalPoint C N n q) = 0
  critical_simple : ∀ n : ℕ+, ∀ q ∈ V,
    deriv (deriv (hillHminusDiscriminant q)) (hillHminusUniformCriticalPoint C N n q) ≠ 0
  numerator_analytic : ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusUniformNumerator C N n) (univ ×ˢ V)
  numerator_free : ∀ n : ℕ+, ∀ z : ℂ, hillHminusUniformNumerator C N n (z,0) = classicalHillFreePsi n z
  numerator_factor : ∀ n : ℕ+, ∀ q ∈ V, ∀ z : ℂ,
    (z-hillHminusUniformCriticalPoint C N n q)*hillHminusUniformNumerator C N n (z,q) =
      (2*(n : ℂ)*Real.pi)*deriv (hillHminusDiscriminant q) z
  numerator_center_ne_zero : ∀ n : ℕ+, ∀ q ∈ V,
    hillHminusUniformNumerator C N n (hillHminusUniformCriticalPoint C N n q,q) ≠ 0
  cover : ∀ k : ℕ+, ∀ q ∈ V, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
    (z^2,q) ∈ hillHminusContinuationDomain
  period_analytic : ∀ n k : ℕ+, AnalyticOnNhd ℂ (hillHminusPeriodEntry C N n k) V
  period_free : ∀ n k : ℕ+, hillHminusPeriodEntry C N n k 0 = if n = k then 1 else 0

/-- One complex Hminus1-open neighborhood supports all actual critical
basis functions, every original contour, and all analytic period entries. -/
theorem exists_hillHminus_all_contour_period_data :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ HillHminusAllContourPeriodData C N V := by
  obtain ⟨C,N,W,hN,hW,h0W,hWC,hcrit,hB,hhigh⟩ := exists_hillHminus_uniform_numerator_basis
  let U : Fin (N+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then (exists_hillHminus_fixed_frequency_contour_neighborhood ⟨i.val,hi⟩).choose else univ
  have hU (i : Fin (N+1)) : IsOpen (U i) ∧ (0 : PeriodOneHminusOne) ∈ U i := by
    by_cases hi : 0 < i.val
    · simpa only [U,dif_pos hi] using
        ⟨(exists_hillHminus_fixed_frequency_contour_neighborhood ⟨i.val,hi⟩).choose_spec.1,
          (exists_hillHminus_fixed_frequency_contour_neighborhood ⟨i.val,hi⟩).choose_spec.2.1⟩
    · simp only [U,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  let V := W ∩ ⋂ i, U i
  have hV : IsOpen V := hW.inter (isOpen_iInter_of_finite fun i => (hU i).1)
  have h0V : (0 : PeriodOneHminusOne) ∈ V := ⟨h0W,mem_iInter.mpr (fun i => (hU i).2)⟩
  have hcover (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
      (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      (z^2,q) ∈ hillHminusContinuationDomain := by
    by_cases hk : (k : ℕ) ≤ N
    · have hi := mem_iInter.mp hq.2 (⟨(k : ℕ),Nat.lt_succ_of_le hk⟩ : Fin (N+1))
      have hqU : q ∈ (exists_hillHminus_fixed_frequency_contour_neighborhood k).choose := by
        simpa only [U,dif_pos k.pos] using! hi
      exact (exists_hillHminus_fixed_frequency_contour_neighborhood k).choose_spec.2.2 q hqU z hz
    · exact hhigh k (Nat.lt_of_not_ge hk) q hq.1 z hz
  refine ⟨C,N,V,hN,{
    isOpen := hV
    zero_mem := h0V
    chart_domain := fun _ hq => hWC hq.1
    critical_free := fun n => (hcrit n).1
    critical_analytic := fun n => (hcrit n).2.1.mono inter_subset_left
    critical_zero := fun n q hq => ((hcrit n).2.2 q hq.1).1
    critical_simple := fun n q hq => ((hcrit n).2.2 q hq.1).2
    numerator_analytic := fun n => (hB n).1.mono (fun _ ht => ⟨ht.1,ht.2.1⟩)
    numerator_free := fun n => (hB n).2.1
    numerator_factor := fun n q hq => ((hB n).2.2 q hq.1).1
    numerator_center_ne_zero := fun n q hq => ((hB n).2.2 q hq.1).2
    cover := hcover
    period_analytic := ?_
    period_free := ?_ }⟩
  · intro n k
    let D := hillHminusContinuationDomain ∩ (univ ×ˢ W)
    have hD : IsOpen D := isOpen_hillHminusContinuationDomain.inter (isOpen_univ.prod hW)
    have hI : AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
        hillHminusUniformNumerator C N n t/hillHminusContinuedRoot t) D := by
      apply ((hB n).1.mono inter_subset_right).div
        (analyticOnNhd_hillHminusContinuedRoot.mono inter_subset_left)
      intro t ht
      exact hillHminusSourceFamily.root_ne_zero t ht.1
    let T : ℂ × PeriodOneHminusOne → ℂ × PeriodOneHminusOne := fun t => (t.1^2,t.2)
    have hT : Continuous T := by fun_prop
    have hG : AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
        (hillHminusUniformNumerator C N n (t.1^2,t.2)/hillHminusContinuedRoot (t.1^2,t.2))*(2*t.1)) (T ⁻¹' D) := by
      intro t ht
      exact ((hI (T t) ht).comp (f := T) ((analyticAt_fst.pow 2).prod analyticAt_snd)).mul
        (analyticAt_const.mul analyticAt_fst)
    exact analyticOnNhd_const.mul (analyticOnNhd_circleIntegral_of_jointAnalytic _ (hD.preimage hT) hG
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) (by positivity) hV
      (fun q hq z hz => ⟨hcover k q hq z hz,mem_univ _,hq.1⟩))
  · intro n k
    unfold hillHminusPeriodEntry
    simp only [(hB n).2.1,hillHminusContinuedRoot_base,circleIntegral_classicalHillFreePsi_frequency]
    split_ifs
    · exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    · exact mul_zero _

end NLS.KdV
