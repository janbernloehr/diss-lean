import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleVanishing
import NLS.ComplexAnalysis.AffineLoopHomotopy

/-!
# Contours close to an isolated midpoint circle

A smooth loop uniformly close to an isolated midpoint circle can be
deformed to that circle through an annulus avoiding every periodic gap.
Its critical-root quotient integral therefore vanishes as well.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Moving the center and radius by small amounts moves the entire
standard circle path by at most their combined distance. -/
theorem sourceCirclePath_dist_le_centers_radii
    (c c' : ℂ) (R R' : ℝ) (u : I) :
    dist (NLS.ComplexAnalysis.circlePath c' R' u)
      (NLS.ComplexAnalysis.circlePath c R u) ≤
      dist c' c + |R'-R| := by
  change dist (circleMap c' R' ((2*Real.pi)*(u:ℝ)))
    (circleMap c R ((2*Real.pi)*(u:ℝ))) ≤ _
  rw [dist_eq_norm, dist_eq_norm]
  have heq :
      circleMap c' R' ((2*Real.pi)*(u:ℝ)) -
        circleMap c R ((2*Real.pi)*(u:ℝ)) =
      (c'-c) + ((R'-R:ℝ):ℂ) * exp (((2*Real.pi)*(u:ℝ))*Complex.I) := by
    simp only [circleMap]
    push_cast
    ring
  rw [heq]
  calc
    ‖(c'-c) + ((R'-R:ℝ):ℂ) * exp (((2*Real.pi)*(u:ℝ))*Complex.I)‖ ≤
        ‖c'-c‖ + ‖((R'-R:ℝ):ℂ) * exp (((2*Real.pi)*(u:ℝ))*Complex.I)‖ :=
      norm_add_le _ _
    _ = ‖c'-c‖ + |R'-R| := by
      have hnorm : ‖exp (((2*Real.pi)*(u:ℝ))*Complex.I)‖ = 1 :=
        by simpa [Complex.ofReal_mul, mul_assoc] using
          (Complex.norm_exp_ofReal_mul_I ((2*Real.pi)*(u:ℝ)))
      simp only [norm_mul, hnorm, mul_one,
        Complex.norm_real, Real.norm_eq_abs]

/-- Every sufficiently close smooth contour inherits the zero integral
of an isolated midpoint circle. The explicit annulus bounds guarantee
that the affine deformation stays away from the selected gap and all
other gaps. -/
theorem sourceCriticalRootRatio_nearMidpointCircleIntegral_eq_zero
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
    ∀ (R r₀ Rmax δ : ℝ), 0 ≤ r₀ → 0 ≤ δ →
      d < R → r₀+δ < R → R+δ ≤ Rmax →
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r₀ →
      closedBall c Rmax ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      ∀ {a : ℂ} (γ : Path a a),
        ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
        (∀ u : I,
          dist (γ u) (NLS.ComplexAnalysis.circlePath c R u) ≤ δ) →
        (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 := by
  dsimp only
  intro R r₀ Rmax δ hr₀ hδ hdR hinner houter hseg hother a γ hγ hclose
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  change d < R at hdR
  have hRpos : 0 < R := by linarith
  have hRmax : R ≤ Rmax := by linarith
  have hfilled : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    (closedBall_subset_closedBall hRmax).trans hother
  have hcircle : (∮ z in C(c,R), f z) = 0 :=
    sourceCriticalRootRatio_midpointCircleIntegral_eq_zero_of_isolated
      hp hp1 ψ hreal n hopen R hdR hfilled
  let H := ContinuousMap.Homotopy.affine
    (NLS.ComplexAnalysis.circlePath c R : C(I, ℂ)) (γ : C(I, ℂ))
  have hannulus (s u : I) :
      r₀ < dist (H (s,u)) c ∧ dist (H (s,u)) c ≤ Rmax :=
    NLS.ComplexAnalysis.affineCircleHomotopy_annulus
      c R r₀ Rmax δ hr₀ hδ hinner houter γ hclose s u
  have havoid : range H ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rintro z ⟨⟨s,u⟩, rfl⟩ m
    by_cases hm : m = n
    · subst m
      intro hz
      have hlt := mem_ball.mp (hseg hz)
      exact (not_lt_of_ge (hannulus s u).1.le) hlt
    · exact (hother (mem_closedBall.mpr (hannulus s u).2)) m hm
  have heq := sourceCriticalRootRatio_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ H
    (NLS.ComplexAnalysis.affineHomotopy_loop (γ₁ := NLS.ComplexAnalysis.circlePath c R)
      (γ₂ := γ)) havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c R) hγ)
  calc
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c R,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq.symm
    _ = (∮ z in C(c,R), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c R
    _ = 0 := hcircle

/-- Nearby circles with moving centers also have zero quotient
integral whenever their center and radius shifts fit the certified
gap-free annulus. -/
theorem sourceCriticalRootRatio_nearMidpointCircle_circleIntegral_eq_zero
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
    ∀ (R r₀ Rmax δ : ℝ), 0 ≤ r₀ → 0 ≤ δ →
      d < R → r₀+δ < R → R+δ ≤ Rmax →
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r₀ →
      closedBall c Rmax ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      ∀ (c' : ℂ) (R' : ℝ), dist c' c + |R'-R| ≤ δ →
        (∮ z in C(c',R'), f z) = 0 := by
  dsimp only
  intro R r₀ Rmax δ hr₀ hδ hdR hinner houter hseg hother c' R' hclose
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have h := sourceCriticalRootRatio_nearMidpointCircleIntegral_eq_zero
    hp hp1 ψ hreal n hopen R r₀ Rmax δ hr₀ hδ hdR hinner houter
    hseg hother (NLS.ComplexAnalysis.circlePath c' R')
    (NLS.ComplexAnalysis.circlePath_contDiffOn c' R')
    (fun u => (sourceCirclePath_dist_le_centers_radii c c' R R' u).trans hclose)
  exact (NLS.ComplexAnalysis.curveIntegral_circlePath f c' R').symm.trans h

end NLS.ZakharovShabat
