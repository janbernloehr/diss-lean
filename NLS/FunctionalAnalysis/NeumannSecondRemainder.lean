import Mathlib.Analysis.Normed.Operator.Banach

/-! A quantitative second-order expansion of any actual corrected
vector, using only its solved equation and a half-size operator bound. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem norm_neumann_second_remainder_le (T : E →L[𝕜] E) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1/2) (hT : ‖T‖ ≤ t) (b g : E) (hg : g-T g=b) :
    ‖g-(b+T b)‖ ≤ 2*t^2*‖b‖ := by
  have hge : g=b+T g := sub_eq_iff_eq_add.mp hg
  have hgnorm : ‖g‖ ≤ 2*‖b‖ := by
    have hn := norm_add_le b (T g)
    rw [← hge] at hn
    have htn := (T.le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (hT.trans ht1) (norm_nonneg g))
    linarith
  have he : g-(b+T b)=T (T g) := by
    have hmap := congrArg T hge
    rw [map_add] at hmap
    calc
      _ = (b+T g)-(b+T b) := congrArg (fun x : E => x-(b+T b)) hge
      _ = T g-T b := by abel
      _ = T (T g) := sub_eq_iff_eq_add.mpr (hmap.trans (add_comm _ _))
  rw [he]
  have htwice : ‖T (T g)‖ ≤ t*(t*‖g‖) :=
    (T.le_opNorm _).trans (mul_le_mul hT
      ((T.le_opNorm g).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg g)))
        (norm_nonneg _) ht)
  exact htwice.trans (by nlinarith [mul_le_mul_of_nonneg_left hgnorm (sq_nonneg t)])

end NLS.FunctionalAnalysis
