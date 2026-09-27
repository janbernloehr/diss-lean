import NLS.ZakharovShabat.SourceGapStadiumCircleLocalGeometry

/-!
# Local holomorphic stadium-to-circle deformation

The stadium-to-circle integral identity only uses differentiability
on a set containing the four affine homotopies. For a real open gap,
the existing cut-avoidance result and the midpoint-disc bound supply
such a set from a local analytic neighborhood.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A four-piece stadium has the same integral as its matching corner
circle whenever an integrand is differentiable on a set containing
every point of the affine deformation. -/
theorem sourceGap_stadium_eq_cornerCirclePath_integral_of_local_differentiable
    (l r c : ℂ) (d ρ : ℝ) (f : ℂ → ℂ) (D : Set ℂ)
    (hf : ∀ z ∈ D, DifferentiableAt ℂ f z)
    (hAI : ∀ s u : I,
      (ContinuousMap.Homotopy.affine
        (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleUpperArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        ((sourceEndpointSemicirclePath r ρ).symm : C(I,ℂ))
        (stadiumCircleRightArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleLowerArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        ((sourceLeftOuterArcPath l ρ).symm : C(I,ℂ))
        (stadiumCircleLeftArc c d ρ : C(I,ℂ))) (s,u) ∈ D) :
    (∫ᶜ z in sourceGapStadiumPath l r ρ,
      holomorphicOneForm f z) =
      ∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
        (stadiumCircleRightArc c d ρ)).trans
        (stadiumCircleLowerArc c d ρ)).trans
        (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z := by
  let upper : Path (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) :=
    Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I)
  let right : Path (r+(ρ:ℂ)*Complex.I) (r-(ρ:ℂ)*Complex.I) :=
    (sourceEndpointSemicirclePath r ρ).symm
  let lower : Path (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) :=
    Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I)
  let left : Path (l-(ρ:ℂ)*Complex.I) (l+(ρ:ℂ)*Complex.I) :=
    (sourceLeftOuterArcPath l ρ).symm
  let cupper := stadiumCircleUpperArc c d ρ
  let cright := stadiumCircleRightArc c d ρ
  let clower := stadiumCircleLowerArc c d ρ
  let cleft := stadiumCircleLeftArc c d ρ
  have hsource {a b c' d' : ℂ} (γ : Path a b) (η : Path c' d')
      (h : ∀ s u : I,
        (ContinuousMap.Homotopy.affine (γ : C(I,ℂ))
          (η : C(I,ℂ))) (s,u) ∈ D) :
      range γ ⊆ D := by
    rintro z ⟨u,rfl⟩
    have hz := h 0 u
    change AffineMap.lineMap (γ u) (η u) (0:ℝ) ∈ D at hz
    simpa only [AffineMap.lineMap_apply_zero] using hz
  have htarget {a b c' d' : ℂ} (γ : Path a b) (η : Path c' d')
      (h : ∀ s u : I,
        (ContinuousMap.Homotopy.affine (γ : C(I,ℂ))
          (η : C(I,ℂ))) (s,u) ∈ D) :
      range η ⊆ D := by
    rintro z ⟨u,rfl⟩
    have hz := h 1 u
    change AffineMap.lineMap (γ u) (η u) (1:ℝ) ∈ D at hz
    simpa only [AffineMap.lineMap_apply_one] using hz
  have huDom := hsource upper cupper (fun s u => (hAI s u).1)
  have hrDom := hsource right cright (fun s u => (hAI s u).2.1)
  have hlDom := hsource lower clower (fun s u => (hAI s u).2.2.1)
  have hleftDom := hsource left cleft (fun s u => (hAI s u).2.2.2)
  have hcuDom := htarget upper cupper (fun s u => (hAI s u).1)
  have hcrDom := htarget right cright (fun s u => (hAI s u).2.1)
  have hclDom := htarget lower clower (fun s u => (hAI s u).2.2.1)
  have hcleftDom := htarget left cleft (fun s u => (hAI s u).2.2.2)
  have hsLeft : ContDiffOn ℝ 2 left.extend (Icc (0:ℝ) 1) := by
    apply sourcePath_symm_contDiffOn_two
    change ContDiffOn ℝ 2 (sourceEndpointSemicirclePath l (-ρ)).extend
      (Icc (0:ℝ) 1)
    exact sourceEndpointSemicirclePath_contDiffOn_two l (-ρ)
  obtain ⟨hcuSmooth,hcrSmooth,hclSmooth,hcleftSmooth⟩ :=
    stadiumCircleArcs_contDiffOn c d ρ
  have hint {a b : ℂ} (γ : Path a b)
      (hsmooth : ContDiffOn ℝ 2 γ.extend (Icc (0:ℝ) 1))
      (hdom : range γ ⊆ D) :
      CurveIntegrable (holomorphicOneForm f) γ := by
    have hω : ContinuousOn (holomorphicOneForm f) (range γ) := by
      intro z hz
      exact (((hf z (hdom hz)).continuousAt).smul
        continuousAt_const).continuousWithinAt
    exact hω.curveIntegrable_of_contDiffOn
      (hsmooth.of_le (by norm_num)) (fun t => ⟨t,rfl⟩)
  change (∫ᶜ z in ((upper.trans right).trans lower).trans left,
    holomorphicOneForm f z) =
    ∫ᶜ z in ((cupper.trans cright).trans clower).trans cleft,
      holomorphicOneForm f z
  apply four_piece_curveIntegral_eq_of_affine_homotopy f (t := D)
  · exact hAI
  · exact hf
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact sourcePath_symm_contDiffOn_two _
      (sourceEndpointSemicirclePath_contDiffOn_two r ρ)
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact hsLeft
  · exact hcuSmooth
  · exact hcrSmooth
  · exact hclSmooth
  · exact hcleftSmooth
  · exact hint upper (sourceSegmentPath_contDiffOn_two _ _) huDom
  · exact hint right (sourcePath_symm_contDiffOn_two _
      (sourceEndpointSemicirclePath_contDiffOn_two r ρ)) hrDom
  · exact hint lower (sourceSegmentPath_contDiffOn_two _ _) hlDom
  · exact hint left hsLeft hleftDom
  · exact hint cupper hcuSmooth hcuDom
  · exact hint cright hcrSmooth hcrDom
  · exact hint clower hclSmooth hclDom
  · exact hint cleft hcleftSmooth hcleftDom

/-- The stadium-to-corner-circle identity holds for an integrand
differentiable only where the selected deformation runs: the root
domain intersected with a fixed filled midpoint disc. -/
theorem exists_sourceGap_stadium_eq_cornerCirclePath_integral_of_local_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (R : ℝ) (f : ℂ → ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R →
    (∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ ∩ closedBall c R,
      DifferentiableAt ℂ f z) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm f z) =
      ∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
        (stadiumCircleRightArc c d ρ)).trans
        (stadiumCircleLowerArc c d ρ)).trans
        (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro hR hf
  change d < R at hR
  let D := sourceCanonicalRootDomain hp hp1 ψ ∩ closedBall c R
  have hfD : ∀ z ∈ D, DifferentiableAt ℂ f z := by
    intro z hz
    exact hf z hz
  obtain ⟨ε₀,hε₀,hroot⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleHomotopy_mem_domain
      hp hp1 ψ hreal n hopen
  let ε := min ε₀ (R-d)
  have hε : 0 < ε := lt_min hε₀ (sub_pos.mpr hR)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
    ⟨hρ.1,hρ.2.trans (min_le_left _ _)⟩
  have hmargin : d+ρ ≤ R := by
    have hbound := hρ.2.trans (min_le_right ε₀ (R-d))
    linarith
  have hAI (s u : I) :
      (ContinuousMap.Homotopy.affine
        (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleUpperArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        ((sourceEndpointSemicirclePath r ρ).symm : C(I,ℂ))
        (stadiumCircleRightArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleLowerArc c d ρ : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine
        ((sourceLeftOuterArcPath l ρ).symm : C(I,ℂ))
        (stadiumCircleLeftArc c d ρ : C(I,ℂ))) (s,u) ∈ D := by
    have hroot' := hroot ρ hρ₀ s u
    have hball := sourceGapStadiumCircleAffine_mem_midpoint_closedBall
      hp hp1 ψ hreal n hopen ρ R hρ.1 hmargin s u
    exact ⟨⟨hroot'.1,hball.1⟩,
      ⟨hroot'.2.1,hball.2.1⟩,
      ⟨hroot'.2.2.1,hball.2.2.1⟩,
      ⟨hroot'.2.2.2,hball.2.2.2⟩⟩
  exact sourceGap_stadium_eq_cornerCirclePath_integral_of_local_differentiable
    l r c d ρ f D hfD hAI

end NLS.ZakharovShabat
