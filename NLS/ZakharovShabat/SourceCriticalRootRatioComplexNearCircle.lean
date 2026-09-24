import NLS.ZakharovShabat.SourceCriticalRootRatioComplexLoopZero

/-!
# Nearby smooth gap contours for complex sources

Explicit inner and outer margins keep the straight-line homotopy of a
nearby smooth contour and the fixed isolating circle away from every
periodic gap. The quotient integral therefore vanishes on that contour
for each complex source in the local neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near an open real-type source gap, every sufficiently close smooth
loop has zero quotient integral for nearby complex sources, provided
the displayed inner and outer margins isolate the same gap. -/
theorem exists_local_sourceCriticalRootRatio_complexNearCircleIntegral_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) n).re) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        (∀ ψ ∈ V, ∀ (r₀ Rmax δ : ℝ),
          0 ≤ r₀ → 0 ≤ δ → r₀ + δ < R → R + δ ≤ Rmax →
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r₀ →
          closedBall c Rmax ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
          ∀ {a : ℂ} (γ : Path a a),
            ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
            (∀ u : I, dist (γ u) (NLS.ComplexAnalysis.circlePath c R u) ≤ δ) →
            (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w) z) = 0) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom,hloopZero⟩ :=
    exists_local_sourceCriticalRootRatio_complexLoopIntegral_zero hp hp1 φ hφ n hopen
  refine ⟨V,hVopen,hφV,c,R,hR,hgeom,?_⟩
  intro ψ hψ r₀ Rmax δ hr₀ hδ hinner houter hseg hother a γ hγ hclose
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
  exact hloopZero ψ hψ γ H
    (NLS.ComplexAnalysis.affineHomotopy_loop
      (γ₁ := NLS.ComplexAnalysis.circlePath c R) (γ₂ := γ))
    havoid
    (NLS.ComplexAnalysis.affineHomotopy_contDiffOn
      (NLS.ComplexAnalysis.circlePath_contDiffOn c R) hγ)

end NLS.ZakharovShabat
