import NLS.ZakharovShabat.LinearWeightRootGap
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Analytic.Order

/-! # The single diagonal root in the proof of Lemma 25.4 -/
noncomputable section
open Set Metric
open scoped NNReal
namespace NLS.ZakharovShabat

/-- The quadratic-threshold diagonal bound gives one simple root on the full strip. -/
theorem exists_unique_section25DiagonalCenter (n : ℤ) (a : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖a z‖ ≤ 1/8) :
    ∃ ζ : ℂ, ζ ∈ refinedResonantDisk n ∧ ‖ζ-(Real.pi : ℂ)*n‖ ≤ 1/8 ∧
      ζ = (Real.pi : ℂ)*n+a ζ ∧
      (∀ z ∈ resonantStrip n, z = (Real.pi : ℂ)*n+a z → z = ζ) ∧
      analyticOrderAt (fun z => z-(Real.pi : ℂ)*n-a z) ζ = 1 := by
  let c : ℂ := (Real.pi : ℂ)*n
  let S : Set ℂ := closedBall c (Real.pi/8)
  have hS : S ⊆ refinedResonantDisk n := by
    intro z hz
    exact (mem_closedBall.mp hz).trans_lt (by linarith [Real.pi_pos])
  have hstrip : S ⊆ resonantStrip n := hS.trans (refinedResonantDisk_subset_strip n)
  let f : S → S := fun z => ⟨c+a z, by
    apply mem_closedBall.mpr
    simpa only [dist_eq_norm,add_sub_cancel_left] using
      (hb z (hstrip z.property)).trans (by linarith [Real.pi_gt_three])⟩
  have hf : ContractingWith (1/6 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (c+a x.val) (c+a y.val) ≤ (1/6 : ℝ)*dist x.val y.val
    simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (ha z (refinedResonantDisk_subset_strip n hz)).differentiableAt)
        (norm_deriv_le_sixth_on_refined_disk n a ha hb) (convex_ball _ _)
        (hS y.property) (hS x.property)
  let : Nonempty S := ⟨⟨c,mem_closedBall_self (by positivity)⟩⟩
  let : CompleteSpace S := (isClosed_closedBall : IsClosed S).completeSpace_coe
  let ζ : ℂ := (hf.fixedPoint f).val
  have hζS : ζ ∈ S := (hf.fixedPoint f).property
  have hζ : ζ = c+a ζ := (congrArg Subtype.val hf.fixedPoint_isFixedPt).symm
  have hsmall : ‖ζ-c‖ ≤ 1/8 := by
    rw [hζ,add_sub_cancel_left]
    exact hb ζ (hstrip hζS)
  refine ⟨ζ,hS hζS,hsmall,hζ,?_,?_⟩
  · intro z hz heq
    have hzS : z ∈ S := by
      apply mem_closedBall.mpr
      rw [dist_eq_norm,heq,add_sub_cancel_left]
      exact (hb z hz).trans (by linarith [Real.pi_gt_three])
    have hfix : Function.IsFixedPt f ⟨z,hzS⟩ := by
      apply Subtype.ext
      exact heq.symm
    exact congrArg Subtype.val (hf.fixedPoint_unique hfix)
  · have he : HasDerivAt (fun z => z-c-a z) (1-deriv a ζ) ζ :=
      ((hasDerivAt_id ζ).sub_const c).sub (ha ζ (hstrip hζS)).differentiableAt.hasDerivAt
    have hn : deriv (fun z => z-c-a z) ζ ≠ 0 := by
      rw [he.deriv]
      intro hzero
      have heq : deriv a ζ = 1 := (sub_eq_zero.mp hzero).symm
      have hbound := norm_deriv_le_sixth_on_refined_disk n a ha hb ζ (hS hζS)
      rw [heq,norm_one] at hbound
      norm_num at hbound
    have han : AnalyticAt ℂ (fun z => z-c-a z) ζ :=
      (analyticAt_id.sub analyticAt_const).sub (ha ζ (hstrip hζS))
    apply han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero _ hn
    change ζ-c-a ζ = 0
    linear_combination hζ

/-- The actual diagonal has its unique simple root in the printed source disc,
at the exact quadratic threshold, without a further large-index condition. -/
theorem linearWeight_diagonal_simple_root (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (n : ℤ) (hn : 8*‖φ‖^2 ≤ 1+|(n:ℝ)|) :
    ∃ ζ : ℂ, ζ ∈ closedBall ((Real.pi : ℂ)*n) (quadraticLocalizationRadius ‖φ‖ n) ∧
      ζ = (Real.pi : ℂ)*n+weightedResonantAExtension (by simp) w φ n ζ ∧
      (∀ z ∈ resonantStrip n,
        z = (Real.pi : ℂ)*n+weightedResonantAExtension (by simp) w φ n z → z = ζ) ∧
      analyticOrderAt (fun z => z-(Real.pi : ℂ)*n-
        weightedResonantAExtension (by simp) w φ n z) ζ = 1 := by
  have hcoef := linearWeight_resonantCoefficients w hw φ n hn
  obtain ⟨ζ,hζ,_,hfix,hunique,horder⟩ := exists_unique_section25DiagonalCenter n _ hcoef.1
    (fun z hz => ((hcoef.2.2.2 z hz).1).trans (quadratic_threshold_diagonal_le n hn))
  refine ⟨ζ,?_,hfix,hunique,horder⟩
  apply mem_closedBall.mpr
  rw [dist_eq_norm,hfix,add_sub_cancel_left]
  apply (hcoef.2.2.2 ζ (refinedResonantDisk_subset_strip n hζ)).1.trans
  unfold quadraticLocalizationRadius
  exact le_add_of_nonneg_right (by positivity)

end NLS.ZakharovShabat
