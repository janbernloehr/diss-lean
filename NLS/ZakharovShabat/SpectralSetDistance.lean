import NLS.ZakharovShabat.FreeDiscSeparation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Infimum distance and quantitative separation of spectral sets

The set distance is the infimum of pointwise distances. Shrinking disjoint
balls and controlling their lattice offsets yields the two-sided index
comparison needed in Lemma 10.1.
-/

noncomputable section
open Set Metric
namespace NLS.ZakharovShabat

/-- Infimum distance between two subsets of the spectral plane. -/
def spectralSetDistance (s t : Set ℂ) : ℝ :=
  Metric.infDist (0 : ℂ) (Set.image2 (fun z w : ℂ => z-w) s t)

/-- Each point pair bounds the infimum distance from above. -/
theorem spectralSetDistance_le_dist {s t : Set ℂ} {z w : ℂ}
    (hz : z ∈ s) (hw : w ∈ t) : spectralSetDistance s t ≤ dist z w := by
  have h : z-w ∈ Set.image2 (fun z w : ℂ => z-w) s t := ⟨z,hz,w,hw,rfl⟩
  simpa only [spectralSetDistance,dist_eq_norm,zero_sub,norm_neg] using
    Metric.infDist_le_dist_of_mem (x := (0 : ℂ)) h

/-- A uniform pointwise lower bound passes to two nonempty sets. -/
theorem le_spectralSetDistance {s t : Set ℂ} (hs : s.Nonempty) (ht : t.Nonempty)
    {r : ℝ} (h : ∀ z ∈ s, ∀ w ∈ t, r ≤ dist z w) : r ≤ spectralSetDistance s t := by
  obtain ⟨z,hz⟩ := hs
  obtain ⟨w,hw⟩ := ht
  apply (Metric.le_infDist (show (Set.image2 (fun z w : ℂ => z-w) s t).Nonempty from
    ⟨z-w,z,hz,w,hw,rfl⟩)).mpr
  rintro _ ⟨a,ha,b,hb,rfl⟩
  simpa only [dist_eq_norm,zero_sub,norm_neg] using h a ha b hb

/-- This distance is literally the greatest lower bound of all pairwise distances. -/
theorem spectralSetDistance_isGLB {s t : Set ℂ} (hs : s.Nonempty) (ht : t.Nonempty) :
    IsGLB {r : ℝ | ∃ z ∈ s, ∃ w ∈ t, dist z w = r} (spectralSetDistance s t) := by
  constructor
  · rintro r ⟨z,hz,w,hw,rfl⟩
    exact spectralSetDistance_le_dist hz hw
  · intro r hr
    exact le_spectralSetDistance hs ht (fun z hz w hw => hr ⟨z,hz,w,hw,rfl⟩)

/-- Shrinking disjoint positive-radius balls creates the sum of the radius margins. -/
theorem shrunk_disjoint_balls_pointwise_separation
    (a b z w : ℂ) (r s dr ds : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hd : Disjoint (ball a r) (ball b s))
    (hz : z ∈ ball a (r-dr)) (hw : w ∈ ball b (s-ds)) :
    dr+ds ≤ dist z w := by
  have hc := (disjoint_ball_ball_iff hr hs).mp hd
  have hz' := mem_ball.mp hz
  have hw' := mem_ball.mp hw
  have htri := dist_triangle4 a z w b
  rw [dist_comm a z] at htri
  linarith

/-- A positive separation and bounded lattice offsets give one index comparison constant. -/
theorem exists_index_comparison_constant (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t d : ℝ, 1 ≤ t → δ ≤ d →
      Real.pi*t ≤ 2*R+d → d ≤ Real.pi*t+2*R →
      c⁻¹*t ≤ d ∧ d ≤ c*t := by
  let L := (1+2*R/δ)/Real.pi
  let B := Real.pi+2*R
  let c := max 1 (max L B)
  have hc : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hLc : L ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hBc : B ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨c,hc,?_⟩
  intro t d ht hd hlow hupp
  have hdpos : 0 < d := hδ.trans_le hd
  have hm := mul_le_mul_of_nonneg_left hd (div_nonneg (by positivity : 0 ≤ 2*R) hδ.le)
  have hcancel : (2*R/δ)*δ = 2*R := div_mul_cancel₀ _ hδ.ne'
  rw [hcancel] at hm
  have hLt : t ≤ L*d := by
    dsimp [L]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith
  have hCt : t ≤ c*d := hLt.trans (mul_le_mul_of_nonneg_right hLc hdpos.le)
  have hB : d ≤ B*t := by
    have hmR := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2*R)
    dsimp [B]
    nlinarith
  constructor
  · rw [mul_comm,← div_eq_mul_inv]
    exact (div_le_iff₀ hcpos).mpr (by nlinarith [hCt])
  · exact hB.trans (mul_le_mul_of_nonneg_right hBc (by linarith))

end NLS.ZakharovShabat
