import NLS.ZakharovShabat.SourcePsiSelectedJacobianInjectivity
import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic

/-!
# Local injectivity of the selected psi root Jacobian

The global holomorphic equation construction already selects a common
real-centered contour family, with every periodic gap inside its circle
and every circle inside its isolating disc. The interpolation argument
therefore applies to its actual bounded root Jacobian throughout the
real locus of that neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near a real-type source, the selected psi root Jacobian is
injective at real root data whose roots lie in the prescribed disjoint
isolating discs. -/
theorem exists_local_sourcePsi_selectedJacobian_injective
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, displacedRoots (a : Coeff p) j ∈
            sourceIsolatingDisc hp hp1 φ Niso εiso j) →
          Function.Injective
            (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcReal,htail,hgeom,
      ⟨Niso,εiso,hcluster,hdisjoint,hfilled⟩,
      C,hC,hcoord,hbound,hrealSeq,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_⟩
  intro a ψ hpair hreal hroots hrootloc
  have hcenter (m : ℤ) : ∃ x : ℝ, c m = (x : ℂ) := by
    refine ⟨(c m).re,?_⟩
    apply Complex.ext
    · rfl
    · simpa using hcReal m
  exact sourcePsiSelectedRootJacobian_injective_of_gapGeometry
    hp hp1 φ Niso εiso n c R U hUopen hcoord hdiff hrealSeq
      a ψ hpair hreal hroots hrootloc hdisjoint hcenter
      (fun m => (hgeom (a,ψ) hpair m).1)
      (fun m => (hgeom (a,ψ) hpair m).2.1)
      hfilled
      (fun m => (hgeom (a,ψ) hpair m).2.2.1)
      (fun m => (hgeom (a,ψ) hpair m).2.2.2)

end NLS.ZakharovShabat
