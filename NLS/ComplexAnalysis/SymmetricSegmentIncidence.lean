import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Closed incidence for a segment specified by symmetric data

The segment joining two complex endpoints depends only on their midpoint
and squared difference. Membership can be expressed with one compact
real parameter and a polynomial equality; this makes the incidence set
closed without choosing a square root or an endpoint order.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- Membership in the segment encoded by its midpoint and squared
endpoint difference. The parameter is compact, including both ends. -/
def SymmetricSegmentIncidence (z m g : ℂ) : Prop :=
  ∃ t : Set.Icc (0 : ℝ) 1,
    (z-m)^2 = ((t.val : ℂ)-1/2)^2*g

/-- A segment has a symmetric polynomial description independent of
which endpoint is called first. -/
theorem mem_segment_iff_symmetricSegmentIncidence (a b z : ℂ) :
    z ∈ segment ℝ a b ↔
      SymmetricSegmentIncidence z ((a+b)/2) ((b-a)^2) := by
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    simp only [AffineMap.lineMap_apply_module', Complex.real_smul]
    ring
  · rintro ⟨⟨t, ht⟩, heq⟩
    have hsquare : (z-(a+b)/2)^2 = (((t : ℂ)-1/2)*(b-a))^2 := by
      simpa only [mul_pow] using heq
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquare with h | h
    · refine ⟨t, ht, ?_⟩
      simp only [AffineMap.lineMap_apply_module', Complex.real_smul]
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      ring
    · refine ⟨1-t, ?_, ?_⟩
      · change 0 ≤ 1-t ∧ 1-t ≤ 1
        change 0 ≤ t ∧ t ≤ 1 at ht
        constructor <;> linarith [ht.1, ht.2]
      simp only [AffineMap.lineMap_apply_module', Complex.real_smul]
      rw [sub_eq_iff_eq_add] at h
      rw [h]
      push_cast
      ring

/-- Segment incidence is closed in the spectral point, midpoint, and
squared difference. -/
theorem isClosed_symmetricSegmentIncidence :
    IsClosed {x : ℂ × ℂ × ℂ |
      SymmetricSegmentIncidence x.1 x.2.1 x.2.2} := by
  let C : Set ((ℂ × ℂ × ℂ) × Set.Icc (0 : ℝ) 1) :=
    {q | (q.1.1-q.1.2.1)^2 = ((q.2.val : ℂ)-1/2)^2*q.1.2.2}
  have hC : IsClosed C := by
    dsimp [C]
    apply isClosed_eq <;> fun_prop
  have hproj : IsClosed ((Prod.fst : (ℂ × ℂ × ℂ) ×
      Set.Icc (0 : ℝ) 1 → ℂ × ℂ × ℂ) '' C) :=
    isClosedMap_fst_of_compactSpace C hC
  convert hproj using 1
  ext x
  simp only [mem_image, SymmetricSegmentIncidence]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(x,t), ht, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq⟩

/-- If the midpoint and squared endpoint difference vary continuously at
a parameter, a spectral point outside its segment stays outside on some
open parameter neighborhood. Individual endpoint continuity is unnecessary. -/
theorem exists_open_avoids_segment_of_symmetric_continuousAt
    {X : Type*} [TopologicalSpace X]
    (a b z : X → ℂ) (x : X)
    (hz : z x ∉ segment ℝ (a x) (b x))
    (hZ : ContinuousAt z x)
    (hM : ContinuousAt (fun y => (a y+b y)/2) x)
    (hG : ContinuousAt (fun y => (b y-a y)^2) x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, z y ∉ segment ℝ (a y) (b y) := by
  let F : X → ℂ × ℂ × ℂ :=
    fun y => (z y, (a y+b y)/2, (b y-a y)^2)
  let C : Set (ℂ × ℂ × ℂ) :=
    {q | SymmetricSegmentIncidence q.1 q.2.1 q.2.2}
  have hF : ContinuousAt F x := hZ.prodMk (hM.prodMk hG)
  have hbase : F x ∈ Cᶜ := by
    change ¬ SymmetricSegmentIncidence (z x) ((a x+b x)/2) ((b x-a x)^2)
    simpa only [← mem_segment_iff_symmetricSegmentIncidence] using hz
  have hnear : F ⁻¹' Cᶜ ∈ 𝓝 x :=
    hF (isClosed_symmetricSegmentIncidence.isOpen_compl.mem_nhds hbase)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  have hnot : ¬ SymmetricSegmentIncidence (z y)
      ((a y+b y)/2) ((b y-a y)^2) := hUsub hy
  simpa only [← mem_segment_iff_symmetricSegmentIncidence] using hnot

end NLS.ComplexAnalysis
