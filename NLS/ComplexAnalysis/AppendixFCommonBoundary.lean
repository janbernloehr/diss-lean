import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic.Module

/-! # A common boundary point for countably many straight gap paths -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis

/-- A real affine line meets a complex circle in finitely many points. -/
theorem appendixF_circle_line_finite (c : ℂ) (R : ℝ) (τ g : ℂ) :
    (sphere c R ∩ Set.range (fun t : ℝ => t • g + τ)).Finite := by
  by_cases h : (sphere c R ∩ Set.range (fun t : ℝ => t • g + τ)).Nonempty
  · obtain ⟨p, hp, t₀, ht₀⟩ := h
    let S : EuclideanGeometry.Sphere ℂ := ⟨c, R⟩
    refine (Set.toFinite ({p, S.secondInter p g} : Set ℂ)).subset ?_
    rintro q ⟨hq, t, ht⟩
    have hline : q ∈ AffineSubspace.mk' p (ℝ ∙ g) := by
      rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
      refine ⟨t-t₀, ?_⟩
      change (t-t₀) • g = q-p
      rw [← ht, ← ht₀]
      module
    have hpS : p ∈ S := hp
    have hqS : q ∈ S := hq
    have he := (S.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hpS hline).mpr hqS
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

/-- One point on a fixed positive-radius circle avoids all lines in a countable family. -/
theorem appendixF_exists_common_boundary_point {ι : Type*} [Countable ι]
    (c : ℂ) (R : ℝ) (hR : 0 < R) (τ g : ι → ℂ) :
    ∃ ν ∈ sphere c R, ∀ k, ν ∉ Set.range (fun t : ℝ => t • g k + τ k) := by
  let bad : Set ℂ := ⋃ k, sphere c R ∩ Set.range (fun t : ℝ => t • g k + τ k)
  have hb : bad.Countable := Set.countable_iUnion fun k =>
    (appendixF_circle_line_finite c R (τ k) (g k)).countable
  have ha := hb.preimage_circleMap c hR.ne'
  obtain ⟨θ, hθ, _⟩ := (ha.dense_compl ℝ).exists_mem_open isOpen_univ Set.univ_nonempty
  refine ⟨circleMap c R θ, circleMap_mem_sphere c hR.le θ, ?_⟩
  intro k hk
  exact hθ (Set.mem_iUnion.mpr ⟨k, circleMap_mem_sphere c hR.le θ, hk⟩)

/-- A noncollinear terminal point keeps the punctured midpoint spoke off the whole gap line. -/
theorem appendixF_midpoint_spoke_avoids_line (τ g ν z : ℂ)
    (hν : ν ∉ Set.range (fun t : ℝ => t • g + τ))
    (hz : z ∈ segment ℝ τ ν) (hzτ : z ≠ τ) :
    z ∉ Set.range (fun t : ℝ => t • g + τ) := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _, rfl⟩ := hz
  have ht : t ≠ 0 := by
    intro h
    simp [h] at hzτ
  rintro ⟨s, hs⟩
  dsimp only at hs
  have he : t • (ν-τ) = s • g := by
    apply add_right_cancel (b := τ)
    rw [hs, AffineMap.lineMap_apply_module]
    module
  have hi := congrArg (fun z : ℂ => t⁻¹ • z) he
  simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at hi
  apply hν
  refine ⟨t⁻¹*s, ?_⟩
  dsimp only
  rw [← hi, sub_add_cancel]

/-- A fixed boundary point gives admissible punctured midpoint spokes for every gap in a
countable family, including zero-length gaps. The entire spoke remains in the closed disc. -/
theorem appendixF_exists_common_midpoint_spokes {ι : Type*} [Countable ι]
    (c : ℂ) (R : ℝ) (hR : 0 < R) (τ g : ι → ℂ)
    (hτ : ∀ k, τ k ∈ closedBall c R) :
    ∃ ν ∈ sphere c R, ∀ k,
      segment ℝ (τ k) ν \ {τ k} ⊆
        closedBall c R \ segment ℝ (τ k-g k) (τ k+g k) := by
  obtain ⟨ν, hν, hlines⟩ := appendixF_exists_common_boundary_point c R hR τ g
  refine ⟨ν, hν, ?_⟩
  intro k z hz
  refine ⟨(convex_closedBall c R).segment_subset (hτ k) (sphere_subset_closedBall hν) hz.1, ?_⟩
  intro hzg
  apply appendixF_midpoint_spoke_avoids_line (τ k) (g k) ν z (hlines k) hz.1
    (by simpa only [Set.mem_singleton_iff] using hz.2)
  rw [segment_eq_image_lineMap] at hzg
  obtain ⟨t, _, rfl⟩ := hzg
  refine ⟨2*t-1, ?_⟩
  rw [AffineMap.lineMap_apply_module]
  module

end NLS.ComplexAnalysis
