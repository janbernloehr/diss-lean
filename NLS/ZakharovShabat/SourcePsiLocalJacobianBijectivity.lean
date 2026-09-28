import NLS.ZakharovShabat.SourcePsiSelectedJacobianIsolatingDiagonal
import NLS.ZakharovShabat.SourcePsiSelectedJacobianInjectivity
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-!
# Local bijectivity of the selected psi root Jacobian

The contour witnesses used for the diagonal-plus-compact decomposition
also satisfy the gap-zero interpolation hypotheses. Thus the bounded
selected root Jacobian is injective, and the Fredholm reduction makes
it bijective at real-type source data with isolated real roots. The
same contour family gives a `C¹` selected equation on an open domain;
its geometry and coordinate formula are retained for the free seed.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected psi equation is `C¹`, and its root Jacobian is a
bounded linear isomorphism throughout the real locus of a common
local contour family, provided the displaced roots lie in their
isolating discs. -/
theorem exists_local_sourcePsi_selectedJacobian_bijective
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ Niso εiso i)
            (sourceIsolatingDisc hp hp1 φ Niso εiso j)) ∧
        (∀ m : ℤ, closedBall (c m) (R m) ⊆
          sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m
              (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        ContDiffOn ℂ 1
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, j ≠ n → displacedRoots (a : Coeff p) j ∈
            sourceIsolatingDisc hp hp1 φ Niso εiso j) →
          Function.Bijective
            (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hcReal,hgeom,hcoord,hrealSeq,hdiff,hdecomp⟩ :=
    exists_local_sourcePsi_selectedJacobian_isolatingDiagonal
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hdisjoint,hfilled,hcReal,hgeom,hcoord,
    NLS.ComplexAnalysis.contDiffOn_one_of_differentiableOn _ hUopen hdiff,?_⟩
  intro a ψ hpair hreal hroots hrootloc
  have hcenter (m : ℤ) : ∃ x : ℝ, c m = (x : ℂ) := by
    refine ⟨(c m).re,?_⟩
    apply Complex.ext
    · rfl
    · simpa using hcReal m
  have hinj := sourcePsiSelectedRootJacobian_injective_of_gapGeometry
    hp hp1 φ Niso εiso n c R U hUopen hcoord hdiff hrealSeq
      a ψ hpair hreal hroots hrootloc hdisjoint hcenter
      (fun m => (hgeom (a,ψ) hpair m).1)
      (fun m => (hgeom (a,ψ) hpair m).2.1)
      hfilled
      (fun m => (hgeom (a,ψ) hpair m).2.2.1)
      (fun m => (hgeom (a,ψ) hpair m).2.2.2)
  obtain ⟨hcompact,hdiag,hQ⟩ :=
    hdecomp a ψ hpair hreal hroots hrootloc
  rw [hQ]
  exact Coeff.bijective_add_compact_of_bijective_of_injective
    _ _ hdiag hcompact (by simpa only [← hQ] using hinj)

end NLS.ZakharovShabat
