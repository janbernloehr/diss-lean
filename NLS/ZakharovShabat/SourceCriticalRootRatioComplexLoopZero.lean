import NLS.ZakharovShabat.SourceCriticalRootRatioCircleComplexNeighborhoodZero
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy
import NLS.ComplexAnalysis.AffineLoopHomotopy

/-!
# Complex-source vanishing for loops deformable to a gap circle

Near an open real-type gap, one fixed circle has zero quotient integral
for all complex source perturbations. Holomorphic homotopy invariance
transfers that zero to every smooth closed loop with a gap-avoiding
smooth homotopy to the circle.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every twice-smooth loop connected to the fixed isolating circle
by a twice-smooth gap-avoiding loop homotopy has zero quotient integral,
uniformly over the same complex source neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_complexLoopIntegral_zero
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
        (∀ ψ ∈ V, ∀ {a : ℂ} (γ : Path a a),
          ∀ H : (NLS.ComplexAnalysis.circlePath c R : C(I, ℂ)).Homotopy γ,
            (∀ s : I, H (s, 1) = H (s, 0)) →
            range H ⊆ sourceCanonicalRootDomain hp hp1 ψ →
            ContDiffOn ℝ 2
              (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
              (Icc 0 1) →
            (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
              (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
                sourceCanonicalRoot hp hp1 ψ w) z) = 0) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero hp hp1 φ hφ n hopen
  refine ⟨V,hVopen,hφV,c,R,hR,hgeom,?_⟩
  intro ψ hψ a γ H hloop havoid hsmooth
  let f : ℂ → ℂ := fun w =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w
  have heq := sourceCriticalRootRatio_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ H hloop havoid hsmooth
  calc
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ᶜ z in NLS.ComplexAnalysis.circlePath c R,
          NLS.ComplexAnalysis.holomorphicOneForm f z := heq.symm
    _ = (∮ z in C(c,R), f z) :=
      NLS.ComplexAnalysis.curveIntegral_circlePath f c R
    _ = 0 := hzero ψ hψ

end NLS.ZakharovShabat
