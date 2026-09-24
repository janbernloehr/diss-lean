import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleCrossing
import NLS.ComplexAnalysis.PiecewiseHolomorphicLoopHomotopy

/-!
# Deforming the critical-root quotient stadium into a corner circle

The four cut-avoiding affine deformations constructed for real
parameters are packaged here as bundled path homotopies. This feeds
the piecewise holomorphic contour homotopy theorem.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The four bundled affine path homotopies all stay in the
canonical-root domain for one common small radius. -/
theorem exists_sourceCriticalRootRatio_stadiumCircleHomotopy_mem_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε, ∀ s u : I,
      (ContinuousMap.Homotopy.affine
        (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleUpperArc c d ρ : C(I,ℂ))) (s,u) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      (ContinuousMap.Homotopy.affine
        ((sourceEndpointSemicirclePath r ρ).symm : C(I,ℂ))
        (stadiumCircleRightArc c d ρ : C(I,ℂ))) (s,u) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      (ContinuousMap.Homotopy.affine
        (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) : C(I,ℂ))
        (stadiumCircleLowerArc c d ρ : C(I,ℂ))) (s,u) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      (ContinuousMap.Homotopy.affine
        ((sourceLeftOuterArcPath l ρ).symm : C(I,ℂ))
        (stadiumCircleLeftArc c d ρ : C(I,ℂ))) (s,u) ∈
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,havoid⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleAffine_mem_domain
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro ρ hρ s u
  have h := havoid ρ hρ (s:ℝ) s.property (u:ℝ) u.property
  simp only [Path.extend_extends'] at h
  change AffineMap.lineMap
      (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) u)
      (stadiumCircleUpperArc c d ρ u) (s:ℝ) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      ((sourceEndpointSemicirclePath r ρ).symm u)
      (stadiumCircleRightArc c d ρ u) (s:ℝ) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) u)
      (stadiumCircleLowerArc c d ρ u) (s:ℝ) ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      ((sourceLeftOuterArcPath l ρ).symm u)
      (stadiumCircleLeftArc c d ρ u) (s:ℝ) ∈
        sourceCanonicalRootDomain hp hp1 ψ
  exact h

/-- A holomorphic integrand has equal integrals on a sufficiently small
gap stadium and the four matching clockwise circle arcs. -/
theorem exists_sourceGap_stadium_eq_cornerCirclePath_integral_of_differentiable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (f : ℂ → ℂ)
    (hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      DifferentiableAt ℂ f z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
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
  let D := sourceCanonicalRootDomain hp hp1 ψ
  obtain ⟨ε,hε,havoid⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleHomotopy_mem_domain
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
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
  have hAI (s u : I) :
      (ContinuousMap.Homotopy.affine (upper : C(I,ℂ))
        (cupper : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine (right : C(I,ℂ))
        (cright : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine (lower : C(I,ℂ))
        (clower : C(I,ℂ))) (s,u) ∈ D ∧
      (ContinuousMap.Homotopy.affine (left : C(I,ℂ))
        (cleft : C(I,ℂ))) (s,u) ∈ D :=
    havoid ρ hρ s u
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

/-- The critical-root quotient integral over a sufficiently small
stadium equals the integral over its four matching clockwise circle
arcs. -/
theorem exists_sourceCriticalRootRatio_stadium_eq_cornerCirclePath_integral
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm f z) =
      ∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
        (stadiumCircleRightArc c d ρ)).trans
        (stadiumCircleLowerArc c d ρ)).trans
        (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z := by
  exact exists_sourceGap_stadium_eq_cornerCirclePath_integral_of_differentiable
    hp hp1 ψ hreal n hopen _ (by
      intro z hz
      exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz).differentiableAt)

end NLS.ZakharovShabat
