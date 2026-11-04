import NLS.KdV.HillBalancedRegularFactorBounds
import NLS.KdV.HillCanonicalZeroSequencePeriods
import NLS.ZakharovShabat.SourceStandardRootQuadraticOffset
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalContourHomotopy

/-! The ACTUAL full Hill period equation gives a zero balanced-factor
period on ANY smaller enclosing circle in its original isolating disc.
The verified reciprocal-root correction then gives a quadratic gap
bound without assuming the desired root asymptotic. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem balancedRegularFactor_zero_period_on_inner_circle (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ht : (d,q) ∈ P.inputDomain) (hF : P.equation n (d,q) = 0)
    (a : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆ ball a R)
    (hball : closedBall a R ⊆ P.discs ((m:ℕ):ℤ)) :
    (∮ z in C(a,R), ((hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),d) ((m:ℕ):ℤ)-z)/
      sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) z)*
        hillBalancedMidpointRegularFactor n m (P.parent.parent.miuraBall.actionBall.shift:ℂ) d (P.sourcePsi q) z) = 0 := by
  let c : ℂ := (P.parent.parent.miuraBall.actionBall.shift:ℂ)
  let k : ℤ := ((m:ℕ):ℤ)
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q ht.2).2 k
    (P.centers k) (P.radii k) (P.radii_pos k) (P.discs_eq k)
  have hclosure : closedBall (P.centers k:ℂ) (P.radii k) = closure (P.discs k) := by
    rw [P.discs_eq,closure_ball _ (P.radii_pos k).ne']
  have hplace : ∀ j : ℤ, hillIndependentFrequency (c,d) j ∈ P.discs j := ht.1.2
  have hC : 0 < P.separation⁻¹ := inv_pos.mpr (zero_lt_one.trans_le P.isolating.one_le)
  have hpoles (z : ℂ) (hz : z ∈ sphere (P.centers k:ℂ) (P.radii k)) :=
    hillIndependent_uniform_paired_pole_distance P.isolating c d hplace n m hmn z (hclosure ▸ sphere_subset_closedBall hz)
  have hzero : hillPeriodEquationWeight n m*hillEnergyProductJointPeriod n (P.centers k:ℂ) (P.radii k)
      (d,(c,P.sourcePsi q)) = 0 := by
    have he := congrArg (fun F : lp (fun _ : ℕ+ => ℂ) 2 => F m) hF
    rw [P.equation_apply n m (d,q) ht] at he
    change P.row n m (d,q) = 0 at he
    simpa only [row,hillProductPeriodEquationRow,if_neg hmn,c,k] using he
  have houter := hillBalancedMidpointRegularFactor_period n m hmn c d (P.sourcePsi q)
    (P.centers k:ℂ) (P.radii k) (P.radii_pos k).le D.sphere_subset_rootDomain
    (fun z hz => norm_pos_iff.mp (hC.trans_le (hpoles z hz).1))
    (fun z hz => norm_pos_iff.mp (hC.trans_le (hpoles z hz).2))
  rw [hzero,mul_zero] at houter
  let f := hillBalancedMidpointRegularFactor n m c d (P.sourcePsi q)
  let g : ℂ → ℂ := fun z => (hillIndependentFrequency (c,d) k-z)*f z
  have hf := analyticOnNhd_hillBalancedMidpointRegularFactor P.quotients P.isolating
    (P.sourcePsi q) (P.image q ht.2).1 (P.image q ht.2).2 c d hplace n m hmn
  have hg : AnalyticOnNhd ℂ g (closure (P.discs k)) :=
    fun z hz => (analyticAt_const.sub analyticAt_id).mul (hf z hz)
  have hnest : closedBall a R ⊆ closedBall (P.centers k:ℂ) (P.radii k) := by
    rw [hclosure]
    exact hball.trans subset_closure
  have he := circleIntegral_weighted_sourceStandardRoot_eq_of_local_nestedCircles (by norm_num) (by norm_num)
    (P.sourcePsi q) k g (closure (P.discs k)) hg a (P.centers k:ℂ) R (P.radii k) hR (P.radii_pos k)
    hseg D.gap hnest (by rw [hclosure])
  have hefun : (fun z => g z/sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) k z) =
      (fun z => ((hillIndependentFrequency (c,d) k-z)/sourceStandardRoot (by norm_num) (by norm_num) (P.sourcePsi q) k z)*f z) := by
    funext z
    dsimp only [g]
    ring
  rw [hefun] at he
  exact he.trans houter

theorem norm_balanced_zero_sequence_frequency_offset_le (P : HillProductEquationPatch)
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ht : (d,q) ∈ P.inputDomain) (hF : P.equation n (d,q) = 0)
    (a : ℂ) (R sep Q c₀ : ℝ) (hR : 0 < R) (hsepPos : 0 < sep) (hQ : 0 ≤ Q) (hc₀ : 0 < c₀)
    (hseg : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) ⊆ ball a R)
    (hball : closedBall a R ⊆ P.discs ((m:ℕ):ℤ))
    (hsep : ∀ z ∈ sphere a R, sep ≤ ‖sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)-z‖)
    (hgap : ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ ≤ sep)
    (hquot : ∀ z ∈ P.discs ((m:ℕ):ℤ),
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) (z,P.frequencySource (d,q))‖ ≤ Q)
    (hlower : c₀ ≤ ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ),P.frequencySource (d,q))‖) :
    ‖hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),d) ((m:ℕ):ℤ)-
      sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖ ≤
        (R*(2*P.separation)/(2*sep^3*c₀))*(2*(1+2*P.separation/P.separation⁻¹)^2*Q)*
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ)‖^2 := by
  let c : ℂ := (P.parent.parent.miuraBall.actionBall.shift:ℂ)
  let k : ℤ := ((m:ℕ):ℤ)
  let f := hillBalancedMidpointRegularFactor n m c d (P.sourcePsi q)
  have hplace : ∀ j : ℤ, hillIndependentFrequency (c,d) j ∈ P.discs j := ht.1.2
  have hf := analyticOnNhd_hillBalancedMidpointRegularFactor P.quotients P.isolating (P.sourcePsi q)
    (P.image q ht.2).1 (P.image q ht.2).2 c d hplace n m hmn
  have hmid := P.isolating.gap (P.sourcePsi q) (P.image q ht.2).2 k (sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (P.sourcePsi q) k)
  have hbound (z : ℂ) (hz : z ∈ P.discs k) : ‖f z‖ ≤ (1+2*P.separation/P.separation⁻¹)^2*Q :=
    norm_hillBalancedMidpointRegularFactor_le P.isolating (P.sourcePsi q) (P.image q ht.2).2 c d hplace n m hmn z hz Q hQ (hquot z hz)
  have hdev (z : ℂ) (hz : z ∈ sphere a R) :
      ‖f z-f (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) k)‖ ≤ 2*(1+2*P.separation/P.separation⁻¹)^2*Q := by
    have h := (norm_sub_le _ _).trans (add_le_add (hbound z (hball (sphere_subset_closedBall hz))) (hbound _ hmid))
    exact h.trans_eq (by ring)
  have hmidvalue := hillBalancedMidpointRegularFactor_midpoint_eq_quotient P.isolating (P.sourcePsi q) (P.image q ht.2).2 c d hplace n m hmn
  apply norm_sourceStandardRoot_zero_period_offset_le (by norm_num) (by norm_num) (P.sourcePsi q) k a
    (hillIndependentFrequency (c,d) k) R hR hseg f (hf.mono (hball.trans subset_closure))
    (P.balancedRegularFactor_zero_period_on_inner_circle n m hmn q d ht hF a R hR hseg hball)
    sep (2*P.separation) (2*(1+2*P.separation/P.separation⁻¹)^2*Q) c₀ hsepPos
    (by have := P.isolating.one_le; positivity) (by positivity) hc₀ hsep hgap
    (fun z hz => P.isolating.uniform_disc_diameter k _ z (hplace k) (hball (sphere_subset_closedBall hz))) hdev
  change c₀ ≤ ‖hillBalancedMidpointRegularFactor n m c d (P.sourcePsi q)
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ))‖
  rw [hmidvalue]
  exact hlower

end NLS.KdV.HillProductEquationPatch
