import NLS.KdV.HillFrequencyScaleBounds
import NLS.KdV.HillPhysicalDirichletPlacement
import NLS.KdV.HillMiuraNormalizedRatioReal

/-! The sum of the ACTUAL AUXILIARY frequency and frequency midpoint
stays bounded below by its positive index on ONE complex native ball.
The real gap placement and FULL-l2 continuity retain every low index. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_physicalDirichletFrequency_add_midpoint_ge_of_real (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ ≤
      ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q+
        sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ := by
  let B := P.parent.parent.miuraBall
  have hqB : q ∈ B.source := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.actionBall.lift q,B.actionBall.lift_real q hqB hr⟩
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)
  let μ := P.physicalDirichletFrequency ((m:ℕ):ℤ) q
  have hτi : τ.im = 0 := by
    have h := B.diracSum_im_eq_zero_of_real m q hqB hr
    change (2*τ).im = 0 at h
    simpa [Complex.mul_im] using h
  have hτp : 0 < τ.re := by
    have h := B.diracSum_re_pos_of_real m q hqB hr
    change 0 < (2*τ).re at h
    have he : (2*τ).re = 2*τ.re := by simp
    rw [he] at h
    linarith
  have hμg : μ ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) :=
    canonicalAuxiliaryPeriodOneRoots_mem_sourcePeriodicSegment_of_realType (by norm_num) (by norm_num)
      .dirichlet (P.sourcePsi q) (P.sourcePsi_real q hq hr) _
  have hμI := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) μ hμg
  have hl : 0 < (canonicalPeriodicLeft (by norm_num) (by norm_num)
      (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) ((m:ℕ):ℤ)).re :=
    hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  have hμp : 0 ≤ μ.re := hl.le.trans hμI.1
  have hτ : (τ.re:ℂ) = τ := by
    simpa only [hτi,Complex.ofReal_zero,zero_mul,add_zero] using Complex.re_add_im τ
  change ‖τ‖ ≤ ‖μ+τ‖
  calc
    _ = τ.re := by rw [← hτ,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hτp]; rfl
    _ ≤ μ.re+τ.re := by linarith
    _ = (μ+τ).re := (Complex.add_re _ _).symm
    _ ≤ _ := Complex.re_le_norm _

theorem exists_real_physicalDirichletFrequency_add_midpoint_index_lower_bound
    (P : HillProductEquationPatch) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ a : ℝ, 0 < a ∧ ∀ m : ℕ+,
      a*(m:ℝ) ≤ ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) q+
        sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ := by
  obtain ⟨a,ha,hbase⟩ := P.exists_real_source_frequency_midpoint_index_lower_bound q hq hr
  exact ⟨a,ha,fun m => (hbase m).trans (P.norm_physicalDirichletFrequency_add_midpoint_ge_of_real q hq hr m)⟩

theorem exists_uniform_physicalDirichletFrequency_add_midpoint_index_lower_bound
    (P : HillProductEquationPatch) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ r a : ℝ, 0 < r ∧ 0 < a ∧ ∀ y ∈ ball q r, ∀ m : ℕ+,
      a*(m:ℝ) ≤ ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) y+
        sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ := by
  obtain ⟨a,ha,hbase⟩ := P.exists_real_physicalDirichletFrequency_add_midpoint_index_lower_bound q hq hr
  let M := fun y => hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift y)+
    sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi y)
  have hμ := (P.parent.parent.analytic_auxiliaryDisplacement q (P.parent.subset (P.subset hq)).1).continuousAt
  have hτ := (continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    (by norm_num) (by norm_num) (P.sourcePsi q) (P.sourcePsi_real q hq hr)).comp (P.analytic_sourcePsi q hq).continuousAt
  have hcont : ContinuousAt M q := hμ.add hτ
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hcont.eventually (ball_mem_nhds (M q) (half_pos ha)))
  refine ⟨r,a/2,hrpos,half_pos ha,?_⟩
  intro y hy m
  have hnorm : ‖M y-M q‖ < a/2 := by simpa only [mem_ball,dist_eq_norm,mem_ofPred_eq] using hball hy
  have hcoord := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (M y-M q) ((m:ℕ):ℤ)).trans_lt hnorm
  have heq : (M y-M q) ((m:ℕ):ℤ) =
      (P.physicalDirichletFrequency ((m:ℕ):ℤ) y+
        sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ))-
      (P.physicalDirichletFrequency ((m:ℕ):ℤ) q+
        sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)) := by
    simp only [M,lp.coeFn_sub,lp.coeFn_add,Pi.sub_apply,Pi.add_apply,
      hillMiuraDirichletDisplacement_apply,sourcePeriodicMidpointDisplacement_apply,
      sourceStandardRootMidpoint,physicalDirichletFrequency]
    ring
  rw [heq] at hcoord
  have htri := norm_le_norm_sub_add
    (P.physicalDirichletFrequency ((m:ℕ):ℤ) q+
      sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))
    (P.physicalDirichletFrequency ((m:ℕ):ℤ) y+
      sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ))
  rw [norm_sub_rev] at htri
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  have hb := hbase m
  nlinarith

end NLS.KdV.HillProductEquationPatch
