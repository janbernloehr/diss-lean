import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ZakharovShabat.SourcePsiGlobalContourFamily

/-!
# Reality of all selected psi equation coordinates

The global real-centered contour family and reflection of the psi
integrand give the real-locus conclusion for every deleted index and
every selected gap, with no separation cutoff or gap-type split.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near any real-type source, one common contour family makes every
psi equation coordinate real for real-type source inputs and real
displaced roots. -/
theorem exists_local_sourcePsi_allRealCoordinates
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        (∀ ψ ∈ V, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 ψ) ∧
        ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
          ∀ n : ℤ, ∀ a : Coeff p,
            (∀ k : ℤ, (displacedRoots a k).im = 0) →
              ∀ m : ℤ,
                (sourcePsiEquationCoordinate hp hp1 n m
                  a ψ (c m) (R m)).im = 0 := by
  obtain ⟨K,V,hVopen,hφV,c,R,hcReal,htail,hgeom⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  refine ⟨K,V,hVopen,hφV,c,R,hcReal,htail,hgeom,?_⟩
  intro ψ hψ hreal n a hroots m
  let x : ℝ := (c m).re
  have hx : (x:ℂ) = c m := by
    apply Complex.ext
    · rfl
    · simpa [x] using (hcReal m).symm
  obtain ⟨hR,_,_,hcircle⟩ := hgeom ψ hψ m
  have hcoord := sourcePsiEquationCoordinate_im_eq_zero_of_realCenteredCircle
    hp hp1 ψ hreal n m a hroots x (R m) hR
      (by simpa only [hx] using hcircle)
  simpa only [hx] using hcoord

end NLS.ZakharovShabat
