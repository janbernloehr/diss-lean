import NLS.ZakharovShabat.SourcePsiGlobalContourFamily
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic

/-!
# Scalar psi equations on common contours near real-type sources

The all-gap contour family lies in the jointly analytic canonical-root
domain. Consequently each scalar contour equation is holomorphic in
both Banach parameters at every point of one common neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near an arbitrary real-type source, the same family of contours
supports all scalar psi equations. The source neighborhood is common
to every root input and every pair of equation indices. -/
theorem exists_local_sourcePsi_allGap_scalarAnalytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∀ ψ ∈ V, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 ψ ∧
          ∀ n : ℤ, ∀ a : Coeff p,
            DifferentiableAt ℂ
              (fun b : Coeff p × CoeffPair p =>
                sourcePsiEquationCoordinate hp hp1 n m
                  b.1 b.2 (c m) (R m)) (a,ψ) := by
  obtain ⟨K,Vcont,hVcontOpen,hφVcont,c,R,htail,hgeom⟩ :=
    exists_local_sourcePsi_allGap_contourFamily hp hp1 φ hφ
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  have hφW : φ ∈ W := hrealW hφ
  let V : Set (CoeffPair p) := Vcont ∩ W
  have hVopen : IsOpen V := hVcontOpen.inter hWopen
  have hφV : φ ∈ V := ⟨hφVcont,hφW⟩
  refine ⟨K,V,hVopen,hφV,c,R,htail,?_⟩
  intro ψ hψ m
  obtain ⟨hR,hseg,hdom,hcircle⟩ := hgeom ψ hψ.1 m
  refine ⟨hR,hseg,hdom,hcircle,?_⟩
  intro n a
  exact differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
    hp hp1 n m a ψ (c m) (R m) hR.le
      W hψ.2 (hdata n).1 (hdata n).2 hcircle

end NLS.ZakharovShabat
