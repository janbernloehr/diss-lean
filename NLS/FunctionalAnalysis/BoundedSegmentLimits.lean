import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.Prod

/-! # Bounded segments with a common weak limit

Segments from a fixed vector to a bounded family stay bounded. If a linear
coordinate converges at the endpoints, it converges along the whole family
of segments, uniformly in their parameter in the unit interval.
-/
noncomputable section
open Set Filter Topology
namespace NLS.BoundedSegmentLimits
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The straight segment from the fixed limit to a varying endpoint. -/
def segment (b a : E) (t : ℝ) : E := b + (t : ℂ) • (a-b)

@[simp] theorem segment_zero (b a : E) : segment b a 0 = b := by simp [segment]
@[simp] theorem segment_one (b a : E) : segment b a 1 = a := by simp [segment]

theorem continuous_segment (b a : E) : Continuous (segment b a) :=
  continuous_const.add (Complex.continuous_ofReal.smul continuous_const)

/-- All interpolation segments of a bounded family form one bounded set. -/
theorem bounded_range_segment {α : Type*} (a : α → E) (b : E)
    (hb : Bornology.IsBounded (range a)) :
    Bornology.IsBounded (range (fun t : α × Icc (0 : ℝ) 1 => segment b (a t.1) t.2)) := by
  obtain ⟨M,hM⟩ := hb.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M+2*‖b‖, ?_⟩
  rintro _ ⟨⟨k,t⟩,rfl⟩
  have ht : ‖(t.val : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1] using t.property.2
  calc
    ‖segment b (a k) t‖ ≤ ‖b‖ + ‖(t.val : ℂ) • (a k-b)‖ := norm_add_le _ _
    _ ≤ ‖b‖ + ‖a k-b‖ := by rw [norm_smul]; nlinarith [norm_nonneg (a k-b)]
    _ ≤ ‖b‖ + (‖a k‖+‖b‖) := by linarith [norm_sub_le (a k) b]
    _ ≤ M+2*‖b‖ := by linarith [hM (a k) ⟨k,rfl⟩]

/-- A converging linear coordinate converges uniformly in the segment parameter.
The product with the top filter expresses one eventual index for all parameters. -/
theorem tendsto_coordinate_segment {α : Type*} {l : Filter α} (a : α → E) (b : E)
    (F : E →ₗ[ℂ] ℂ) (ht : Tendsto (fun k => F (a k)) l (𝓝 (F b))) :
    Tendsto (fun t : α × Icc (0 : ℝ) 1 => F (segment b (a t.1) t.2))
      (l ×ˢ ⊤) (𝓝 (F b)) := by
  have hbound : IsBoundedUnder (· ≤ ·) (l ×ˢ (⊤ : Filter (Icc (0 : ℝ) 1)))
      (fun t : α × Icc (0 : ℝ) 1 => ‖(t.2.val : ℂ)‖) := by
    apply isBoundedUnder_of
    refine ⟨1, fun t => ?_⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.2.property.1] using t.2.property.2
  have hdiff : Tendsto (fun t : α × Icc (0 : ℝ) 1 => F (a t.1)-F b)
      (l ×ˢ ⊤) (𝓝 0) := by simpa only [sub_self, Function.comp_def] using (ht.sub_const (F b)).comp tendsto_fst
  have h := (hbound.smul_tendsto_zero hdiff).const_add (F b)
  simpa only [segment, map_add, map_smul, map_sub, add_zero] using h

end NLS.BoundedSegmentLimits
