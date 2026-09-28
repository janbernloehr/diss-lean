import NLS.ZakharovShabat.SourcePsiEquationAllGapZero
import NLS.ZakharovShabat.SourcePsiSelectedJacobianIsolatingDiagonal
import NLS.ZakharovShabat.SourcePsiRootPlacementDomain

/-!
# Gap placement of roots solving the local psi equation

The contour family used for local Jacobian bijectivity also identifies
the roots of a real zero of the selected psi equation. Each retained
root must lie in its own periodic gap, as in the first paragraph of
Proposition 12.9.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- In a common local contour family, every real solution of the
selected psi equation with localized retained roots places those
roots in their corresponding periodic gaps. -/
theorem exists_local_sourcePsi_selectedEquation_solution_roots_mem_gaps
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
          (∀ k : ℤ, k ≠ n →
            displacedRoots (a : Coeff p) k ∈
              sourceIsolatingDisc hp hp1 φ Niso εiso k) →
          sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0 →
          ∀ m : ℤ, m ≠ n →
            displacedRoots (a : Coeff p) m ∈
              sourcePeriodicSegment hp hp1 ψ m := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hcenter,hgeom,hcoord,_,_,_⟩ :=
    exists_local_sourcePsi_selectedJacobian_isolatingDiagonal
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_⟩
  intro a ψ hpair hψ hroots hrootloc hzero
  exact retainedRoots_mem_periodicSegments_of_selectedEquation_zero
    hp hp1 φ ψ hψ Niso εiso n a hroots hrootloc hdisjoint c R
      hcenter (fun m => hgeom (a,ψ) hpair m) hfilled
      (fun m => hcoord (a,ψ) hpair m) hzero

/-- The root-in-gap conclusion holds on the open local domain defined
by retained-root placement, matching the geometry used for local
Jacobian bijectivity. -/
theorem exists_local_sourcePsi_solution_roots_mem_gaps_on_rootPlacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        IsOpen (U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0 →
          ∀ m : ℤ, m ≠ n →
            displacedRoots (a : Coeff p) m ∈
              sourcePeriodicSegment hp hp1 ψ m := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,hgap⟩ :=
    exists_local_sourcePsi_selectedEquation_solution_roots_mem_gaps
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n),?_⟩
  intro a ψ hmem hψ hroots hzero
  exact hgap a ψ hmem.1 hψ hroots hmem.2 hzero

end NLS.ZakharovShabat
