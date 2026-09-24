import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral
import NLS.ComplexAnalysis.PiecewiseHolomorphicLoopHomotopy

/-!
# Affine deformations of the gap stadium pieces

Each straight side and endpoint semicircle is twice smooth on its
parameter interval. Their dependence on the signed radius is affine,
so an affine homotopy between two radii follows the corresponding
piece at the interpolated radius.
-/

noncomputable section
open Set Complex
open scoped unitInterval
namespace NLS.ZakharovShabat

/-- The endpoint arc is twice smooth on its parameter interval. -/
theorem sourceEndpointSemicirclePath_contDiffOn_two
    (c : ℂ) (R : ℝ) :
    ContDiffOn ℝ 2 (sourceEndpointSemicirclePath c R).extend
      (Icc (0:ℝ) 1) := by
  have hsmooth : ContDiff ℝ 2
      (fun t : ℝ => circleMap c R (-(Real.pi/2)+Real.pi*t)) := by
    exact (contDiff_circleMap c R).comp (by fun_prop)
  apply hsmooth.contDiffOn.congr
  intro t ht
  rw [(sourceEndpointSemicirclePath c R).extend_apply ht]
  rfl

/-- A straight segment is twice smooth on its parameter interval. -/
theorem sourceSegmentPath_contDiffOn_two (a b : ℂ) :
    ContDiffOn ℝ 2 (Path.segment a b).extend
      (Icc (0:ℝ) 1) := by
  have hsmooth : ContDiff ℝ 2
      (fun t : ℝ => AffineMap.lineMap a b t) :=
    AffineMap.contDiff_lineMap a b
  apply hsmooth.contDiffOn.congr
  intro t ht
  rw [(Path.segment a b).extend_apply ht]
  rfl

/-- Reversing a twice-smooth path preserves twice-smoothness on the
unit interval. -/
theorem sourcePath_symm_contDiffOn_two {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 2 γ.extend (Icc (0:ℝ) 1)) :
    ContDiffOn ℝ 2 γ.symm.extend (Icc (0:ℝ) 1) := by
  rw [Path.extend_symm]
  apply hγ.comp (by fun_prop)
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

/-- At a fixed angle, the circle map is affine in its signed radius. -/
theorem circleMap_affine_radius (c : ℂ) (R₀ R₁ : ℝ) (s θ : ℝ) :
    AffineMap.lineMap (circleMap c R₀ θ) (circleMap c R₁ θ) s =
      circleMap c ((1-s)*R₀+s*R₁) θ := by
  simp only [AffineMap.lineMap_apply_module, circleMap, Complex.real_smul]
  push_cast
  ring

/-- The affine homotopy of two endpoint arcs is the endpoint arc at
the interpolated signed radius. -/
theorem sourceEndpointSemicirclePath_affine_radius
    (c : ℂ) (R₀ R₁ : ℝ) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (sourceEndpointSemicirclePath c R₀ : C(I, ℂ))
      (sourceEndpointSemicirclePath c R₁ : C(I, ℂ))) (s,u) =
      sourceEndpointSemicirclePath c
        ((1-(s:ℝ))*R₀+(s:ℝ)*R₁) u := by
  change AffineMap.lineMap
    (circleMap c R₀ (-(Real.pi/2)+Real.pi*(u:ℝ)))
    (circleMap c R₁ (-(Real.pi/2)+Real.pi*(u:ℝ))) (s:ℝ) = _
  exact circleMap_affine_radius c R₀ R₁ s _

/-- The affine homotopy of horizontally shifted segments is the
segment shifted by the interpolated radius. -/
theorem sourceShiftedSegmentPath_affine_radius
    (a b : ℂ) (R₀ R₁ : ℝ) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (Path.segment (a+(R₀:ℂ)*Complex.I) (b+(R₀:ℂ)*Complex.I) : C(I, ℂ))
      (Path.segment (a+(R₁:ℂ)*Complex.I) (b+(R₁:ℂ)*Complex.I) : C(I, ℂ))) (s,u) =
      Path.segment
        (a+(((1-(s:ℝ))*R₀+(s:ℝ)*R₁:ℝ):ℂ)*Complex.I)
        (b+(((1-(s:ℝ))*R₀+(s:ℝ)*R₁:ℝ):ℂ)*Complex.I) u := by
  change AffineMap.lineMap
    (AffineMap.lineMap (a+(R₀:ℂ)*Complex.I) (b+(R₀:ℂ)*Complex.I) (u:ℝ))
    (AffineMap.lineMap (a+(R₁:ℂ)*Complex.I) (b+(R₁:ℂ)*Complex.I) (u:ℝ)) (s:ℝ) = _
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
    Complex.real_smul]
  push_cast
  ring

/-- The reversed right endpoint arc also follows the interpolated
radius under an affine homotopy. -/
theorem sourceEndpointSemicirclePath_symm_affine_radius
    (c : ℂ) (R₀ R₁ : ℝ) (s u : I) :
    (ContinuousMap.Homotopy.affine
      ((sourceEndpointSemicirclePath c R₀).symm : C(I, ℂ))
      ((sourceEndpointSemicirclePath c R₁).symm : C(I, ℂ))) (s,u) =
      (sourceEndpointSemicirclePath c
        ((1-(s:ℝ))*R₀+(s:ℝ)*R₁)).symm u := by
  change AffineMap.lineMap
    (sourceEndpointSemicirclePath c R₀ (σ u))
    (sourceEndpointSemicirclePath c R₁ (σ u)) (s:ℝ) = _
  exact sourceEndpointSemicirclePath_affine_radius c R₀ R₁ s (σ u)

/-- The reversed left outer arc follows the interpolated positive
stadium radius; the underlying circle map has negative signed radius. -/
theorem sourceLeftOuterArcPath_symm_affine_radius
    (c : ℂ) (R₀ R₁ : ℝ) (s u : I) :
    (ContinuousMap.Homotopy.affine
      ((sourceLeftOuterArcPath c R₀).symm : C(I, ℂ))
      ((sourceLeftOuterArcPath c R₁).symm : C(I, ℂ))) (s,u) =
      (sourceLeftOuterArcPath c
        ((1-(s:ℝ))*R₀+(s:ℝ)*R₁)).symm u := by
  change AffineMap.lineMap
    (sourceEndpointSemicirclePath c (-R₀) (σ u))
    (sourceEndpointSemicirclePath c (-R₁) (σ u)) (s:ℝ) = _
  have h := sourceEndpointSemicirclePath_affine_radius
    c (-R₀) (-R₁) s (σ u)
  have hr : (1-(s:ℝ))*(-R₀)+(s:ℝ)*(-R₁) =
      -((1-(s:ℝ))*R₀+(s:ℝ)*R₁) := by ring
  rw [hr] at h
  exact h

/-- The lower horizontal side follows the interpolated positive
stadium radius under an affine homotopy. -/
theorem sourceLowerSegmentPath_affine_radius
    (a b : ℂ) (R₀ R₁ : ℝ) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (Path.segment (b-(R₀:ℂ)*Complex.I) (a-(R₀:ℂ)*Complex.I) : C(I, ℂ))
      (Path.segment (b-(R₁:ℂ)*Complex.I) (a-(R₁:ℂ)*Complex.I) : C(I, ℂ))) (s,u) =
      Path.segment
        (b-(((1-(s:ℝ))*R₀+(s:ℝ)*R₁:ℝ):ℂ)*Complex.I)
        (a-(((1-(s:ℝ))*R₀+(s:ℝ)*R₁:ℝ):ℂ)*Complex.I) u := by
  change AffineMap.lineMap
    (AffineMap.lineMap (b-(R₀:ℂ)*Complex.I) (a-(R₀:ℂ)*Complex.I) (u:ℝ))
    (AffineMap.lineMap (b-(R₁:ℂ)*Complex.I) (a-(R₁:ℂ)*Complex.I) (u:ℝ)) (s:ℝ) = _
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
    Complex.real_smul]
  push_cast
  ring

/-- The interval of admissible positive stadium radii is preserved by
affine interpolation. -/
theorem sourceStadium_affine_radius_mem_Ioc
    (ε R₀ R₁ : ℝ) (hR₀ : R₀ ∈ Ioc 0 ε)
    (hR₁ : R₁ ∈ Ioc 0 ε) (s : I) :
    (1-(s:ℝ))*R₀+(s:ℝ)*R₁ ∈ Ioc 0 ε := by
  have h := (convex_Ioc (0:ℝ) ε).lineMap_mem hR₀ hR₁ s.property
  simpa only [AffineMap.lineMap_apply_module, smul_eq_mul] using h

/-- If all sufficiently small stadiums lie in a domain, then every
piece of the affine homotopy between two such stadiums lies there too. -/
theorem sourceGapStadiumPieces_affine_mem
    (l r : ℂ) (ε R₀ R₁ : ℝ) (D : Set ℂ)
    (hR₀ : R₀ ∈ Ioc 0 ε) (hR₁ : R₁ ∈ Ioc 0 ε)
    (hdom : ∀ R ∈ Ioc 0 ε,
      range (sourceGapStadiumPath l r R) ⊆ D)
    (s u : I) :
    (ContinuousMap.Homotopy.affine
      (Path.segment (l+(R₀:ℂ)*Complex.I) (r+(R₀:ℂ)*Complex.I) : C(I, ℂ))
      (Path.segment (l+(R₁:ℂ)*Complex.I) (r+(R₁:ℂ)*Complex.I) : C(I, ℂ)))
        (s,u) ∈ D ∧
    (ContinuousMap.Homotopy.affine
      ((sourceEndpointSemicirclePath r R₀).symm : C(I, ℂ))
      ((sourceEndpointSemicirclePath r R₁).symm : C(I, ℂ)))
        (s,u) ∈ D ∧
    (ContinuousMap.Homotopy.affine
      (Path.segment (r-(R₀:ℂ)*Complex.I) (l-(R₀:ℂ)*Complex.I) : C(I, ℂ))
      (Path.segment (r-(R₁:ℂ)*Complex.I) (l-(R₁:ℂ)*Complex.I) : C(I, ℂ)))
        (s,u) ∈ D ∧
    (ContinuousMap.Homotopy.affine
      ((sourceLeftOuterArcPath l R₀).symm : C(I, ℂ))
      ((sourceLeftOuterArcPath l R₁).symm : C(I, ℂ)))
        (s,u) ∈ D := by
  let R := (1-(s:ℝ))*R₀+(s:ℝ)*R₁
  have hR : R ∈ Ioc 0 ε := sourceStadium_affine_radius_mem_Ioc ε R₀ R₁ hR₀ hR₁ s
  let upper : Path (l+(R:ℂ)*Complex.I) (r+(R:ℂ)*Complex.I) :=
    Path.segment (l+(R:ℂ)*Complex.I) (r+(R:ℂ)*Complex.I)
  let right : Path (r+(R:ℂ)*Complex.I) (r-(R:ℂ)*Complex.I) :=
    (sourceEndpointSemicirclePath r R).symm
  let lower : Path (r-(R:ℂ)*Complex.I) (l-(R:ℂ)*Complex.I) :=
    Path.segment (r-(R:ℂ)*Complex.I) (l-(R:ℂ)*Complex.I)
  let left : Path (l-(R:ℂ)*Complex.I) (l+(R:ℂ)*Complex.I) :=
    (sourceLeftOuterArcPath l R).symm
  have hD := hdom R hR
  change range (((upper.trans right).trans lower).trans left) ⊆ D at hD
  rw [Path.trans_range, Path.trans_range, Path.trans_range] at hD
  have hu : range upper ⊆ D :=
    fun _ hz => hD (Or.inl (Or.inl (Or.inl hz)))
  have hr : range right ⊆ D :=
    fun _ hz => hD (Or.inl (Or.inl (Or.inr hz)))
  have hd : range lower ⊆ D :=
    fun _ hz => hD (Or.inl (Or.inr hz))
  have hl : range left ⊆ D :=
    fun _ hz => hD (Or.inr hz)
  constructor
  · rw [sourceShiftedSegmentPath_affine_radius]
    exact hu ⟨u, rfl⟩
  constructor
  · rw [sourceEndpointSemicirclePath_symm_affine_radius]
    exact hr ⟨u, rfl⟩
  constructor
  · rw [sourceLowerSegmentPath_affine_radius]
    exact hd ⟨u, rfl⟩
  · rw [sourceLeftOuterArcPath_symm_affine_radius]
    exact hl ⟨u, rfl⟩

end NLS.ZakharovShabat
