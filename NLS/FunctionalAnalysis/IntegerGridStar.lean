import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-! # Open integer-grid stars with bounded overlap

The oscillation of the coordinate errors, including a fixed zero error,
is less than one. These open stars cover the real coordinate space. The
vertices of stars meeting at one point form a coordinatewise chain, and
each coordinate takes at most two adjacent integer values.
-/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis
universe u
variable {ι : Type u}

/-- An open star at an integer vertex in the standard simplex subdivision. -/
def integerGridStar (v : ι → ℤ) : Set (ι → ℝ) :=
  {x | (∀ i, -1 < x i - v i ∧ x i - v i < 1) ∧
    ∀ i j, (x i - v i) - (x j - v j) < 1}

theorem isOpen_integerGridStar [Fintype ι] (v : ι → ℤ) : IsOpen (integerGridStar v) := by
  have hc (i) : Continuous (fun x : ι → ℝ => x i - (v i : ℝ)) :=
    (continuous_apply i).sub continuous_const
  rw [show integerGridStar v =
    (⋂ i, {x | -1 < x i - (v i : ℝ)} ∩ {x | x i - (v i : ℝ) < 1}) ∩
      (⋂ i, ⋂ j, {x | (x i - (v i : ℝ)) - (x j - (v j : ℝ)) < 1}) by
        ext x; simp [integerGridStar]]
  exact (isOpen_iInter_of_finite (fun i => (isOpen_lt continuous_const (hc i)).inter
    (isOpen_lt (hc i) continuous_const))).inter
    (isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
      isOpen_lt ((hc i).sub (hc j)) continuous_const)))

/-- The star at the coordinatewise floor contains the point. -/
theorem mem_integerGridStar_floor (x : ι → ℝ) : x ∈ integerGridStar (fun i => ⌊x i⌋) := by
  constructor
  · intro i
    have h0 := Int.floor_le (x i)
    have h1 := Int.lt_floor_add_one (x i)
    constructor <;> linarith
  · intro i j
    have h0 := Int.floor_le (x j)
    have h1 := Int.lt_floor_add_one (x i)
    linarith

/-- Vertices of stars containing x use only the floor and its successor in each coordinate. -/
theorem integerGridStar_vertex_bounds {x : ι → ℝ} {v : ι → ℤ}
    (h : x ∈ integerGridStar v) (i : ι) : ⌊x i⌋ ≤ v i ∧ v i ≤ ⌊x i⌋ + 1 := by
  have h0 := Int.floor_le (x i)
  have h1 := Int.lt_floor_add_one (x i)
  have hv := h.1 i
  constructor
  · have hr : (⌊x i⌋ : ℝ) < (v i : ℝ)+1 := by linarith
    have hi : ⌊x i⌋ < v i+1 := by exact_mod_cast hr
    omega
  · have hr : (v i : ℝ) < (⌊x i⌋ : ℝ)+2 := by linarith
    have hi : v i < ⌊x i⌋+2 := by exact_mod_cast hr
    omega

/-- All integer vertices whose stars contain a fixed point are comparable. -/
theorem integerGridStar_vertices_comparable {x : ι → ℝ} {v w : ι → ℤ}
    (hv : x ∈ integerGridStar v) (hw : x ∈ integerGridStar w) : v ≤ w ∨ w ≤ v := by
  by_cases h : v ≤ w
  · exact Or.inl h
  · right
    by_contra h'
    obtain ⟨i,hi⟩ : ∃ i, w i < v i := by simpa only [Pi.le_def,not_forall,not_le] using h
    obtain ⟨j,hj⟩ : ∃ j, v j < w j := by simpa only [Pi.le_def,not_forall,not_le] using h'
    have hiR : (w i : ℝ)+1 ≤ v i := by exact_mod_cast hi
    have hjR : (v j : ℝ)+1 ≤ w j := by exact_mod_cast hj
    have hvp := hv.2 j i
    have hwp := hw.2 i j
    linarith

/-- Integer translations preserve the shape of a grid star. -/
theorem integerGridStar_translate (x : ι → ℝ) (v z : ι → ℤ) :
    (fun i => x i + z i) ∈ integerGridStar (v+z) ↔ x ∈ integerGridStar v := by
  simp only [integerGridStar,mem_ofPred_eq,Pi.add_apply,Int.cast_add,add_sub_add_right_eq_sub]

/-- Two points in one star differ by less than two in every coordinate. -/
theorem integerGridStar_coordinate_dist_lt_two {v : ι → ℤ} {x y : ι → ℝ}
    (hx : x ∈ integerGridStar v) (hy : y ∈ integerGridStar v) (i : ι) :
    |x i - y i| < 2 := by
  rw [abs_lt]
  have hx' := hx.1 i
  have hy' := hy.1 i
  constructor <;> linarith

end NLS.FunctionalAnalysis
