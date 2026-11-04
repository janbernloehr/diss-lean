import NLS.KdV.HillSourceMidpointGapContinuity
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.FunctionalAnalysis.NonzeroSequenceLowerBound

/-! Strict positive physical Miura midpoints and the free tail give
one lower bound proportional to the original positive index. FULL-l2
midpoint continuity preserves it on ONE complex native source ball. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem source_frequency_midpoint_ne_zero_of_real (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ≠ 0 := by
  have hpos := P.parent.parent.miuraBall.diracSum_re_pos_of_real m q (P.parent.subset (P.subset hq)).1 hr
  intro hz
  change 0 < (2*sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)).re at hpos
  rw [hz,mul_zero,zero_re] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_real_source_frequency_midpoint_index_lower_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ a : ℝ, 0 < a ∧ ∀ m : ℕ+,
      a*(m:ℝ) ≤ ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ := by
  obtain ⟨K,V,_,hbase,htiny⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (P.sourcePsi q)
  let s : Finset ℕ+ := (Finset.range K).image (fun j => (⟨j+1,by omega⟩ : ℕ+))
  let f : ℕ+ → ℂ := fun m => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)/((m:ℕ):ℂ)
  obtain ⟨δ,hδ,hhead⟩ := exists_positive_lower_norm_on_finset f s (fun m _ => div_ne_zero
    (P.source_frequency_midpoint_ne_zero_of_real q hq hr m) (by exact_mod_cast m.ne_zero))
  refine ⟨min (Real.pi/2) δ,lt_min (half_pos Real.pi_pos) hδ,?_⟩
  intro m
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast m.pos
  by_cases hm : K ≤ (m:ℕ)
  · have hmid := (htiny (P.sourcePsi q) hbase ((m:ℕ):ℤ) (by simpa only [Int.natAbs_natCast] using hm)).1
    have htri := norm_le_norm_sub_add ((Real.pi:ℂ)*((m:ℕ):ℤ))
      (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast] at htri
    simp only [Int.cast_natCast] at htri hmid
    rw [abs_of_nonneg hmpos.le] at htri
    rw [norm_sub_rev] at htri
    have hsmall : (Real.pi/2)*(m:ℝ) ≤ ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ := by
      nlinarith [Real.pi_pos]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hmpos.le).trans hsmall
  · have hms : m ∈ s := by
      apply Finset.mem_image.mpr
      refine ⟨(m:ℕ)-1,Finset.mem_range.mpr (by omega),?_⟩
      apply Subtype.ext
      change (m:ℕ)-1+1 = (m:ℕ)
      have := m.pos
      omega
    have h := hhead m hms
    dsimp only [f] at h
    rw [norm_div,Complex.norm_natCast] at h
    have hsmall := (le_div_iff₀ hmpos).mp h
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hmpos.le).trans hsmall

theorem exists_uniform_source_frequency_midpoint_index_lower_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r a : ℝ, 0 < r ∧ 0 < a ∧ ∀ y ∈ ball q r, ∀ m : ℕ+,
      a*(m:ℝ) ≤ ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ := by
  obtain ⟨a,ha,hbase⟩ := P.exists_real_source_frequency_midpoint_index_lower_bound q hq hr
  let M := fun y => sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi y)
  have hcont : ContinuousAt M q := (continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    (by norm_num) (by norm_num) (P.sourcePsi q) (P.sourcePsi_real q hq hr)).comp (P.analytic_sourcePsi q hq).continuousAt
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hcont.eventually (ball_mem_nhds (M q) (half_pos ha)))
  refine ⟨r,a/2,hrpos,half_pos ha,?_⟩
  intro y hy m
  have hnorm : ‖M y-M q‖ < a/2 := by simpa only [mem_ball,dist_eq_norm,mem_ofPred_eq] using hball hy
  have hcoord := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (M y-M q) ((m:ℕ):ℤ)).trans_lt hnorm
  simp only [M,lp.coeFn_sub,Pi.sub_apply,sourcePeriodicMidpointDisplacement_apply,sub_sub_sub_cancel_right] at hcoord
  have htri := norm_le_norm_sub_add
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ))
  rw [norm_sub_rev] at htri
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  have hb := hbase m
  nlinarith

end NLS.KdV.HillProductEquationPatch
