import NLS.KdV.HillFrequencyMidpointUniformLowerBound
import NLS.ZakharovShabat.SourceIsolatingUniformPoleBounds

/-! Uniform frequency scales near every physical real native source.
Positive midpoints stay comparable to their original positive indices;
placed actual numerator roots have the same upper scale. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_uniform_source_frequency_midpoint_index_upper_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ y ∈ ball q r, ∀ m : ℕ+,
      ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤ B*(m:ℝ) := by
  let M := fun y => sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi y)
  have hcont : ContinuousAt M q := (continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    (by norm_num) (by norm_num) (P.sourcePsi q) (P.sourcePsi_real q hq hr)).comp (P.analytic_sourcePsi q hq).continuousAt
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp
    (hcont.norm.eventually (Iio_mem_nhds (show ‖M q‖ < ‖M q‖+1 by linarith)))
  let T := ‖M q‖+1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  refine ⟨r,Real.pi+T,hrpos,by positivity,?_⟩
  intro y hy m
  have hbound : ‖M y‖ ≤ T := (show ‖M y‖ < T from hball hy).le
  have hcoord := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (M y) ((m:ℕ):ℤ)).trans hbound
  have heq : sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ) =
      (Real.pi:ℂ)*((m:ℕ):ℤ)+M y ((m:ℕ):ℤ) := by
    rw [sourcePeriodicMidpointDisplacement_apply]
    ring
  rw [heq]
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  calc
    _ ≤ ‖(Real.pi:ℂ)*((m:ℕ):ℤ)‖+‖M y ((m:ℕ):ℤ)‖ := norm_add_le _ _
    _ ≤ Real.pi*(m:ℝ)+T := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
      simp only [Int.cast_natCast,abs_of_nonneg (show (0:ℝ) ≤ (m:ℝ) by positivity)]
      exact add_le_add le_rfl hcoord
    _ ≤ (Real.pi+T)*(m:ℝ) := by nlinarith

theorem exists_common_actual_frequency_scale_bounds (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r a B : ℝ, 0 < r ∧ 0 < a ∧ 0 ≤ B ∧ ball q r ⊆ P.source ∧
      ∀ y ∈ ball q r, ∀ m : ℕ+,
        a*(m:ℝ) ≤ ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ∧
        ∀ n : ℕ+,
          ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)+
            sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)‖ ≤ B*(m:ℝ) := by
  obtain ⟨rP,hrP,_,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  obtain ⟨rA,a,hrA,ha,hlower⟩ := P.exists_uniform_source_frequency_midpoint_index_lower_bound q hq hr
  obtain ⟨rB,B₀,hrB,hB₀,hupper⟩ := P.exists_uniform_source_frequency_midpoint_index_upper_bound q hq hr
  let r := min rP (min rA rB)
  have hrpos : 0 < r := lt_min hrP (lt_min hrA hrB)
  have hrp : r ≤ rP := min_le_left _ _
  have hra : r ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ rB := (min_le_right _ _).trans (min_le_right _ _)
  let B := 2*B₀+2*P.separation
  have hC : 0 ≤ P.separation := zero_le_one.trans P.isolating.one_le
  refine ⟨r,a,B,hrpos,ha,by dsimp only [B]; positivity,
    (fun y hy => (hperiod y (ball_subset_ball hrp hy) 1).1.2),?_⟩
  intro y hy m
  refine ⟨hlower y (ball_subset_ball hra hy) m,?_⟩
  intro n
  let β := hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusCanonicalZeroSequence n y) ((m:ℕ):ℤ)
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)
  have hper := hperiod y (ball_subset_ball hrp hy) n
  have hmid := P.isolating.gap (P.sourcePsi y) (P.image y hper.1.2).2 ((m:ℕ):ℤ)
    (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ))
  have hdist : ‖β-τ‖ ≤ 2*P.separation := P.isolating.uniform_disc_diameter ((m:ℕ):ℤ) β τ (hper.1.1.2 _) hmid
  have hτ : ‖τ‖ ≤ B₀*(m:ℝ) := hupper y (ball_subset_ball hrb hy) m
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast m.property
  calc
    _ = ‖(β-τ)+2*τ‖ := by congr 1; ring
    _ ≤ ‖β-τ‖+‖2*τ‖ := norm_add_le _ _
    _ ≤ 2*P.separation+2*‖τ‖ := by rw [norm_mul,Complex.norm_ofNat]; exact add_le_add hdist le_rfl
    _ ≤ B*(m:ℝ) := by dsimp only [B]; nlinarith

end NLS.KdV.HillProductEquationPatch
