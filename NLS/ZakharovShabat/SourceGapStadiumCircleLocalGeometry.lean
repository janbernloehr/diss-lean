import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleHomotopy

/-!
# A local disc containing the stadium-to-circle deformation

All four affine path homotopies stay in a filled midpoint disc once
the disc contains both gap endpoints with room for the stadium height.
This geometric fact lets subsequent contour theorems assume local
holomorphy instead of holomorphy on the entire root domain.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem circleMap_mem_enlarged_closedBall
    (a c : ℂ) (d ρ q R : ℝ)
    (ha : a ∈ closedBall c d) (hq : |q| ≤ ρ) (hR : d+ρ ≤ R)
    (θ : ℝ) : circleMap a q θ ∈ closedBall c R := by
  have hcircle : dist (circleMap a q θ) a = |q| :=
    circleMap_mem_sphere' a q θ
  have htriangle := dist_triangle (circleMap a q θ) a c
  exact mem_closedBall.mpr (by linarith [mem_closedBall.mp ha])

private theorem cornerCircleArc_mem_closedBall
    (c : ℂ) (d ρ R : ℝ) (hd : 0 < d) (hρ : 0 < ρ)
    (hR : d+ρ ≤ R) (θ : ℝ) :
    circleMap c (stadiumCornerRadius d ρ) θ ∈ closedBall c R := by
  have hrad := (stadiumCornerRadius_sub_halfWidth hd hρ).2
  have hsphere : dist (circleMap c (stadiumCornerRadius d ρ) θ) c =
      stadiumCornerRadius d ρ :=
    circleMap_mem_sphere c (norm_nonneg _) θ
  exact mem_closedBall.mpr (by linarith)

/-- The four affine homotopies between a gap stadium and its corner
circle remain in any filled disc whose radius exceeds `d + ρ`, provided
both stadium endpoints are within distance `d` of its center. -/
theorem sourceGapStadiumCircleAffine_mem_closedBall
    (l r c : ℂ) (d ρ R : ℝ)
    (hl : l ∈ closedBall c d) (hr : r ∈ closedBall c d)
    (hd : 0 < d) (hρ : 0 < ρ) (hR : d+ρ ≤ R)
    (s u : I) :
    (ContinuousMap.Homotopy.affine
      (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) : C(I,ℂ))
      (stadiumCircleUpperArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      ((sourceEndpointSemicirclePath r ρ).symm : C(I,ℂ))
      (stadiumCircleRightArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) : C(I,ℂ))
      (stadiumCircleLowerArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      ((sourceLeftOuterArcPath l ρ).symm : C(I,ℂ))
      (stadiumCircleLeftArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R := by
  let T := closedBall c R
  have hqpos : |ρ| ≤ ρ := by rw [abs_of_pos hρ]
  have hqneg : |-ρ| ≤ ρ := by rw [abs_neg, abs_of_pos hρ]
  have hUL : l+(ρ:ℂ)*Complex.I ∈ T := by
    rw [← circleMap_pi_div_two]
    exact circleMap_mem_enlarged_closedBall l c d ρ ρ R hl hqpos hR _
  have hUR : r+(ρ:ℂ)*Complex.I ∈ T := by
    rw [← circleMap_pi_div_two]
    exact circleMap_mem_enlarged_closedBall r c d ρ ρ R hr hqpos hR _
  have hLR : r-(ρ:ℂ)*Complex.I ∈ T := by
    rw [← circleMap_neg_pi_div_two]
    exact circleMap_mem_enlarged_closedBall r c d ρ ρ R hr hqpos hR _
  have hLL : l-(ρ:ℂ)*Complex.I ∈ T := by
    rw [← circleMap_neg_pi_div_two]
    exact circleMap_mem_enlarged_closedBall l c d ρ ρ R hl hqpos hR _
  have hupper : (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I)) u ∈ T := by
    change AffineMap.lineMap (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) (u:ℝ) ∈ T
    exact (convex_closedBall c R).lineMap_mem hUL hUR u.property
  have hlower : (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I)) u ∈ T := by
    change AffineMap.lineMap (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) (u:ℝ) ∈ T
    exact (convex_closedBall c R).lineMap_mem hLR hLL u.property
  have hrightRange :
      range ((sourceEndpointSemicirclePath r ρ).symm) ⊆ T := by
    rw [Path.symm_range]
    exact sourceEndpointSemicirclePath_range_subset r ρ T
      (fun θ _ => circleMap_mem_enlarged_closedBall
        r c d ρ ρ R hr hqpos hR θ)
  have hleftRange :
      range ((sourceLeftOuterArcPath l ρ).symm) ⊆ T := by
    rw [Path.symm_range]
    change range (sourceEndpointSemicirclePath l (-ρ)) ⊆ T
    exact sourceEndpointSemicirclePath_range_subset l (-ρ) T
      (fun θ _ => circleMap_mem_enlarged_closedBall
        l c d ρ (-ρ) R hl hqneg hR θ)
  have hright : ((sourceEndpointSemicirclePath r ρ).symm) u ∈ T :=
    hrightRange ⟨u,rfl⟩
  have hleft : ((sourceLeftOuterArcPath l ρ).symm) u ∈ T :=
    hleftRange ⟨u,rfl⟩
  have hcircle (θ : ℝ) :
      circleMap c (stadiumCornerRadius d ρ) θ ∈ T :=
    cornerCircleArc_mem_closedBall c d ρ R hd hρ hR θ
  have hcu : stadiumCircleUpperArc c d ρ u ∈ T := by
    change circleMap c (stadiumCornerRadius d ρ)
      (stadiumUpperLeftAngle d ρ +
        (stadiumUpperRightAngle d ρ-stadiumUpperLeftAngle d ρ)*(u:ℝ)) ∈ T
    exact hcircle _
  have hcr : stadiumCircleRightArc c d ρ u ∈ T := by
    change circleMap c (stadiumCornerRadius d ρ)
      (stadiumUpperRightAngle d ρ +
        (stadiumLowerRightAngle d ρ-stadiumUpperRightAngle d ρ)*(u:ℝ)) ∈ T
    exact hcircle _
  have hcl : stadiumCircleLowerArc c d ρ u ∈ T := by
    change circleMap c (stadiumCornerRadius d ρ)
      (stadiumLowerRightAngle d ρ +
        (stadiumLowerLeftAngle d ρ-stadiumLowerRightAngle d ρ)*(u:ℝ)) ∈ T
    exact hcircle _
  have hcL : stadiumCircleLeftArc c d ρ u ∈ T := by
    change circleMap c (stadiumCornerRadius d ρ)
      (stadiumLowerLeftAngle d ρ +
        (stadiumUpperLeftAngle d ρ-2*Real.pi-
          stadiumLowerLeftAngle d ρ)*(u:ℝ)) ∈ T
    exact hcircle _
  repeat rw [ContinuousMap.Homotopy.affine_apply]
  change
    AffineMap.lineMap _ _ (s:ℝ) ∈ T ∧
    AffineMap.lineMap _ _ (s:ℝ) ∈ T ∧
    AffineMap.lineMap _ _ (s:ℝ) ∈ T ∧
    AffineMap.lineMap _ _ (s:ℝ) ∈ T
  exact ⟨(convex_closedBall c R).lineMap_mem hupper hcu s.property,
    (convex_closedBall c R).lineMap_mem hright hcr s.property,
    (convex_closedBall c R).lineMap_mem hlower hcl s.property,
    (convex_closedBall c R).lineMap_mem hleft hcL s.property⟩

/-- For a real open periodic gap, the stadium-to-circle homotopy stays
in the midpoint disc of radius `R` whenever `d + ρ ≤ R`. -/
theorem sourceGapStadiumCircleAffine_mem_midpoint_closedBall
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d+ρ ≤ R → ∀ s u : I,
    (ContinuousMap.Homotopy.affine
      (Path.segment (l+(ρ:ℂ)*Complex.I) (r+(ρ:ℂ)*Complex.I) : C(I,ℂ))
      (stadiumCircleUpperArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      ((sourceEndpointSemicirclePath r ρ).symm : C(I,ℂ))
      (stadiumCircleRightArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      (Path.segment (r-(ρ:ℂ)*Complex.I) (l-(ρ:ℂ)*Complex.I) : C(I,ℂ))
      (stadiumCircleLowerArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R ∧
    (ContinuousMap.Homotopy.affine
      ((sourceLeftOuterArcPath l ρ).symm : C(I,ℂ))
      (stadiumCircleLeftArc c d ρ : C(I,ℂ))) (s,u) ∈ closedBall c R := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro hR s u
  change d+ρ ≤ R at hR
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hc : c.im = 0 := by simp [c]
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hleftre : l.re-c.re = -d := by dsimp [c,d]; ring
  have hrightre : r.re-c.re = d := by dsimp [c,d]; ring
  have hleftdist : dist l c = d := by
    rw [sourceRealPoints_dist_eq_abs_re_sub l c hends.1 hc, hleftre,
      abs_neg, abs_of_pos hd]
  have hrightdist : dist r c = d := by
    rw [sourceRealPoints_dist_eq_abs_re_sub r c hends.2 hc, hrightre,
      abs_of_pos hd]
  have hleft : l ∈ closedBall c d := mem_closedBall.mpr hleftdist.le
  have hright : r ∈ closedBall c d := mem_closedBall.mpr hrightdist.le
  exact sourceGapStadiumCircleAffine_mem_closedBall l r c d ρ R
    hleft hright hd hρ hR s u

end NLS.ZakharovShabat
