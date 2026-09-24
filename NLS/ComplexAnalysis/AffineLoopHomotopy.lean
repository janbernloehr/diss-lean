import NLS.ComplexAnalysis.CircleCurveIntegral
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Affine homotopies of smooth closed loops

The affine homotopy between two twice-smooth closed paths is smooth.
For a path uniformly close to a circle, every intermediate loop stays
in an explicit annulus about that circle's center.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval ENNReal
namespace NLS.ComplexAnalysis

/-- The affine homotopy between twice-smooth paths is twice smooth
on the unit square. -/
theorem affineHomotopy_contDiffOn
    {a b c d : ℂ} {γ₁ : Path a b} {γ₂ : Path c d}
    (hγ₁ : ContDiffOn ℝ 2 γ₁.extend (Icc 0 1))
    (hγ₂ : ContDiffOn ℝ 2 γ₂.extend (Icc 0 1)) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one
        ((ContinuousMap.Homotopy.affine
          (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))).extend xy.1) xy.2)
      (Icc 0 1) := by
  let H := ContinuousMap.Homotopy.affine (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))
  have hproj : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => xy.2) (Icc 0 1) := by fun_prop
  have hmap : MapsTo (fun xy : ℝ × ℝ => xy.2) (Icc 0 1) (Icc 0 1) := by
    intro xy hxy
    exact ⟨hxy.1.2, hxy.2.2⟩
  have h₁ : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => γ₁.extend xy.2) (Icc 0 1) :=
    hγ₁.comp hproj hmap
  have h₂ : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => γ₂.extend xy.2) (Icc 0 1) :=
    hγ₂.comp hproj hmap
  have hraw : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ =>
      (1-xy.1) • γ₁.extend xy.2 + xy.1 • γ₂.extend xy.2) (Icc 0 1) := by
    fun_prop
  apply hraw.congr
  intro xy hxy
  have hs : xy.1 ∈ (Icc 0 1 : Set ℝ) := ⟨hxy.1.1, hxy.2.1⟩
  have hu : xy.2 ∈ (Icc 0 1 : Set ℝ) := ⟨hxy.1.2, hxy.2.2⟩
  rw [Set.IccExtend_of_mem zero_le_one _ hu]
  rw [H.extend_apply_of_mem_I hs]
  rw [ContinuousMap.Homotopy.affine_apply]
  rw [γ₁.extend_apply hu, γ₂.extend_apply hu]
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  ring

/-- The unit-interval circle path is twice smooth on its parameter
interval. -/
theorem circlePath_contDiffOn (c : ℂ) (R : ℝ) :
    ContDiffOn ℝ 2 (circlePath c R).extend (Icc 0 1) := by
  have hθ : ContDiff ℝ 2 (fun t : ℝ => (2*Real.pi)*t) := by fun_prop
  have hθc : ContDiff ℝ 2 (fun t : ℝ => (((2*Real.pi)*t : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hθ)
  have hraw : ContDiff ℝ 2
      (fun t : ℝ => circleMap c R ((2*Real.pi)*t)) := by
    simp only [circleMap]
    fun_prop
  apply hraw.contDiffOn.congr
  intro t ht
  rw [(circlePath c R).extend_apply ht]
  rfl

/-- The affine homotopy of two loops is a loop at every time. -/
theorem affineHomotopy_loop
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (s : I) :
    (ContinuousMap.Homotopy.affine (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))) (s, 1) =
      (ContinuousMap.Homotopy.affine (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))) (s, 0) := by
  simp [ContinuousMap.Homotopy.affine_apply]

/-- Every intermediate point in an affine deformation stays within the
same uniform distance of the source path. -/
theorem affineHomotopy_dist_left_le
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (ε : ℝ) (hε : 0 ≤ ε)
    (hclose : ∀ u : I, dist (γ₂ u) (γ₁ u) ≤ ε)
    (s u : I) :
    dist ((ContinuousMap.Homotopy.affine
      (γ₁ : C(I, ℂ)) (γ₂ : C(I, ℂ))) (s,u)) (γ₁ u) ≤ ε := by
  rw [ContinuousMap.Homotopy.affine_apply]
  change dist (AffineMap.lineMap (γ₁ u) (γ₂ u) (s:ℝ)) (γ₁ u) ≤ ε
  rw [dist_lineMap_left]
  have hs0 : 0 ≤ (s:ℝ) := s.property.1
  have hs1 : (s:ℝ) ≤ 1 := s.property.2
  rw [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hεs : (s:ℝ)*ε ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hε]
  have hc : dist (γ₁ u) (γ₂ u) ≤ ε := by simpa only [dist_comm] using hclose u
  exact (mul_le_mul_of_nonneg_left hc hs0).trans hεs

/-- A uniform perturbation of a circle admits an affine deformation
confined between explicit inner and outer radii. -/
theorem affineCircleHomotopy_annulus
    (c : ℂ) (R r₀ Rmax ε : ℝ)
    (hr₀ : 0 ≤ r₀) (hε : 0 ≤ ε)
    (hinner : r₀+ε < R) (houter : R+ε ≤ Rmax)
    {a : ℂ} (γ : Path a a)
    (hclose : ∀ u : I, dist (γ u) (circlePath c R u) ≤ ε)
    (s u : I) :
    r₀ < dist ((ContinuousMap.Homotopy.affine
      (circlePath c R : C(I, ℂ)) (γ : C(I, ℂ))) (s,u)) c ∧
    dist ((ContinuousMap.Homotopy.affine
      (circlePath c R : C(I, ℂ)) (γ : C(I, ℂ))) (s,u)) c ≤ Rmax := by
  let H := ContinuousMap.Homotopy.affine
    (circlePath c R : C(I, ℂ)) (γ : C(I, ℂ))
  have hR : 0 ≤ R := by linarith
  have hcircle : dist (circlePath c R u) c = R := by
    change dist (circleMap c R ((2*Real.pi)*(u:ℝ))) c = R
    rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_nonneg hR]
  have hstep : dist (H (s,u)) (circlePath c R u) ≤ ε :=
    affineHomotopy_dist_left_le ε hε hclose s u
  have htri₁ : R ≤ dist (H (s,u)) (circlePath c R u) + dist (H (s,u)) c := by
    calc
      R = dist (circlePath c R u) c := hcircle.symm
      _ ≤ dist (circlePath c R u) (H (s,u)) + dist (H (s,u)) c :=
        dist_triangle _ _ _
      _ = dist (H (s,u)) (circlePath c R u) + dist (H (s,u)) c := by
        rw [dist_comm (circlePath c R u) (H (s,u))]
  have htri₂ : dist (H (s,u)) c ≤
      dist (H (s,u)) (circlePath c R u) + R := by
    calc
      dist (H (s,u)) c ≤
          dist (H (s,u)) (circlePath c R u) + dist (circlePath c R u) c :=
        dist_triangle _ _ _
      _ = dist (H (s,u)) (circlePath c R u) + R := by rw [hcircle]
  constructor <;> linarith

end NLS.ComplexAnalysis
