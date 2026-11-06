import NLS.KdV.HillHminusOneIsospectralLabels
import NLS.KdV.HillHminusOneAllGapSquares
import NLS.ComplexAnalysis.CoshLogBoundaryUniqueness

/-! # The actual real H^-1 primitive depends only on the discriminant

The physical upper real-part sign fixes the exponential sheet. The exact
zero value at the intrinsic lowest endpoint fixes its full logarithm
period. Reflection and full boundary limits then identify both half-plane
branches and the complete real-cut primitive.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusContinuedPrimitive_eq_of_discriminant_eq_upper
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    EqOn (fun z => hillHminusContinuedPrimitive (z,q)) (fun z => hillHminusContinuedPrimitive (z,p))
      {z : ℂ | 0 < z.im} := by
  let c := hillHminusRealLabels q hq 0
  have hlabels := hillHminusRealLabels_eq_of_discriminant_eq q p hq hp hD
  have hqc : hillHminusUpperBoundaryPrimitive q c = 0 := by
    simpa only [c,show (0+1)/2=0 by norm_num,Nat.cast_zero,mul_zero,zero_mul] using
      hillHminusUpperBoundaryPrimitive_label_indexed q hq 0
  have hpc : hillHminusUpperBoundaryPrimitive p c = 0 := by
    have hc : c = hillHminusRealLabels p hp 0 := congrFun hlabels 0
    rw [hc]
    simpa only [show (0+1)/2=0 by norm_num,Nat.cast_zero,mul_zero,zero_mul] using
      hillHminusUpperBoundaryPrimitive_label_indexed p hp 0
  have hqlim := tendsto_hillHminusUpperBoundaryPrimitive_all q hq c
  have hplim := tendsto_hillHminusUpperBoundaryPrimitive_all p hp c
  rw [hqc] at hqlim
  rw [hpc] at hplim
  let := real_upper_nhds_neBot c
  have hexp (z : ℂ) (hz : 0 < z.im) :
      exp (hillHminusContinuedPrimitive (z,q)) = exp (hillHminusContinuedPrimitive (z,p)) := by
    apply exp_eq_of_cosh_eq_of_re_pos _ _
      (hillHminusContinuedPrimitive_re_pos q hq z hz) (hillHminusContinuedPrimitive_re_pos p hp z hz)
    have hqt := (hillHminusContinuedPrimitive_trace (z,q)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz.ne')).1
    have hpt := (hillHminusContinuedPrimitive_trace (z,p)
      (mem_hillHminusContinuationDomain_of_im_ne_zero p hp z hz.ne')).1
    rw [congrFun hD z] at hqt
    linear_combination (hqt-hpt)/2
  exact continuousLogarithms_eqOn_of_common_boundary_limit _ _ _ (convex_halfSpace_im_gt 0).isPreconnected
    (((analyticOnNhd_hillHminusContinuedPrimitive_off_real q hq).mono (fun _ hz => hz.ne')).continuousOn)
    (((analyticOnNhd_hillHminusContinuedPrimitive_off_real p hp).mono (fun _ hz => hz.ne')).continuousOn)
    hexp I (by simp) c 0 hqlim hplim

theorem hillHminusContinuedPrimitive_eq_of_discriminant_eq_off_real
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) (z : ℂ) (hz : z.im ≠ 0) :
    hillHminusContinuedPrimitive (z,q) = hillHminusContinuedPrimitive (z,p) := by
  rcases lt_or_gt_of_ne hz with hl | hu
  · have hi : 0 < (conj z).im := by simpa only [conj_im,neg_pos] using hl
    have he := hillHminusContinuedPrimitive_eq_of_discriminant_eq_upper q p hq hp hD hi
    dsimp only at he
    rw [hillHminusContinuedPrimitive_conj q hq z (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz),
      hillHminusContinuedPrimitive_conj p hp z (mem_hillHminusContinuationDomain_of_im_ne_zero p hp z hz)] at he
    have h := congrArg (fun w : ℂ => -conj w) he
    simpa only [map_neg,conj_conj,neg_neg] using h
  · exact hillHminusContinuedPrimitive_eq_of_discriminant_eq_upper q p hq hp hD hu

theorem hillHminusUpperBoundaryPrimitive_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) (x : ℝ) :
    hillHminusUpperBoundaryPrimitive q x = hillHminusUpperBoundaryPrimitive p x := by
  let := real_upper_nhds_neBot x
  apply tendsto_nhds_unique (tendsto_hillHminusUpperBoundaryPrimitive_all q hq x)
  apply (tendsto_hillHminusUpperBoundaryPrimitive_all p hp x).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hillHminusContinuedPrimitive_eq_of_discriminant_eq_off_real q p hq hp hD z hz.ne').symm

theorem hillHminusRealCutPrimitive_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    hillHminusRealCutPrimitive q = hillHminusRealCutPrimitive p := by
  funext z
  by_cases hz : z.im = 0
  · simp only [hillHminusRealCutPrimitive,if_pos hz]
    exact hillHminusUpperBoundaryPrimitive_eq_of_discriminant_eq q p hq hp hD z.re
  · simp only [hillHminusRealCutPrimitive,if_neg hz]
    exact hillHminusContinuedPrimitive_eq_of_discriminant_eq_off_real q p hq hp hD z hz

theorem hillHminusRealCutRoot_eq_of_discriminant_eq
    (q p : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p)
    (hD : hillHminusDiscriminant q = hillHminusDiscriminant p) :
    hillHminusRealCutRoot q = hillHminusRealCutRoot p := by
  funext z
  rw [hillHminusRealCutRoot,hillHminusRealCutRoot,hillHminusRealCutPrimitive_eq_of_discriminant_eq q p hq hp hD]

end NLS.KdV
