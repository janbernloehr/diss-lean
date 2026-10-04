import NLS.SequenceSpaces.NonnegativeActionIdentity
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! # Uniqueness on overlapping action balls

Two intersecting balls with nonnegative centers contain a nonnegative point
in their intersection. Holomorphic uniqueness therefore propagates agreement
on nonnegative actions to their entire complex overlap.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A point on the segment joining the centers lies in both intersecting
balls, and remains nonnegative. No interior of the cone is needed. -/
theorem exists_nonnegative_mem_ball_inter (a b : Coeff q) (r s : ℝ)
    (ha : a ∈ nonnegativeLocus q) (hb : b ∈ nonnegativeLocus q)
    (h : (ball a r ∩ ball b s).Nonempty) :
    ∃ c ∈ ball a r ∩ ball b s, c ∈ nonnegativeLocus q := by
  obtain ⟨z, hza, hzb⟩ := h
  have hr : 0 < r := (dist_nonneg.trans_lt hza)
  have hs : 0 < s := (dist_nonneg.trans_lt hzb)
  have hrs : 0 < r + s := add_pos hr hs
  have hd : dist a b < r + s := by
    calc
      dist a b ≤ dist a z + dist z b := dist_triangle _ _ _
      _ < r + s := add_lt_add (by simpa only [mem_ball, dist_comm] using hza) hzb
  let t := r / (r + s)
  have ht : 0 < t := div_pos hr hrs
  have ht1 : t < 1 := (div_lt_one hrs).mpr (by linarith)
  have htr : t * (r + s) = r := div_mul_cancel₀ r (ne_of_gt hrs)
  have hts : (1 - t) * (r + s) = s := by nlinarith [htr]
  refine ⟨AffineMap.lineMap a b t, ⟨?_, ?_⟩, ?_⟩
  · change dist (AffineMap.lineMap a b t) a < r
    rw [dist_lineMap_left, Real.norm_of_nonneg ht.le]
    calc
      t * dist a b < t * (r + s) := mul_lt_mul_of_pos_left hd ht
      _ = r := htr
  · change dist (AffineMap.lineMap a b t) b < s
    rw [dist_lineMap_right, Real.norm_of_nonneg (by linarith : 0 ≤ 1 - t)]
    calc
      (1 - t) * dist a b < (1 - t) * (r + s) := mul_lt_mul_of_pos_left hd (by linarith)
      _ = s := hts
  · exact (convex_nonnegativeLocus q).segment_subset ha hb
      (lineMap_mem_segment ℝ a b ⟨ht.le, ht1.le⟩)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Analytic maps on balls centered at nonnegative actions agree on their
whole overlap if they agree on its nonnegative part. Empty overlaps are allowed. -/
theorem eqOn_ball_inter_of_nonnegativeActions_agreement (hp : p ≠ ⊤)
    (f g : Coeff q → F) (a b : Coeff q) (r s : ℝ)
    (ha : a ∈ nonnegativeLocus q) (hb : b ∈ nonnegativeLocus q)
    (hf : DifferentiableOn ℂ f (ball a r)) (hg : DifferentiableOn ℂ g (ball b s))
    (he : ∀ c ∈ ball a r ∩ ball b s, c ∈ nonnegativeLocus q → f c = g c) :
    EqOn f g (ball a r ∩ ball b s) := by
  by_cases h : (ball a r ∩ ball b s).Nonempty
  · obtain ⟨c, hc, hcpos⟩ := exists_nonnegative_mem_ball_inter a b r s ha hb h
    exact eqOn_of_nonnegativeActions_agreement hp f g _ (isOpen_ball.inter isOpen_ball)
      ((convex_ball a r).inter (convex_ball b s)) c hc hcpos
      (hf.mono inter_subset_left) (hg.mono inter_subset_right) he
  · intro c hc
    exact (h ⟨c, hc⟩).elim

end NLS.Coeff
