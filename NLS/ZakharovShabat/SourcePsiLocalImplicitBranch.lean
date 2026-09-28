import NLS.ZakharovShabat.SourcePsiAnalyticImplicitStep
import NLS.ZakharovShabat.SourcePsiRootPlacementDomain

/-!
# Local implicit branches for the selected psi equation

The selected contour family giving the real-locus Jacobian
isomorphism also gives a `C¹` Banach-valued equation and supports the
analytic implicit branch through a solution, once joint analyticity
is available at the solution point.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On a common local contour family, the equation is `C¹`. Within
the open retained-root placement domain, joint analyticity at a real
solution gives an analytic local solution branch. -/
theorem exists_local_sourcePsi_analytic_branch_of_joint_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ContDiffOn ℂ 1
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U ∧
        IsOpen (U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0 →
          AnalyticAt ℂ
            (fun t : DeletedCoeff p n × CoeffPair p =>
              sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
            (a,ψ) →
          ∃ s : CoeffPair p → DeletedCoeff p n,
            AnalyticAt ℂ s ψ ∧ s ψ = a ∧
            ∀ᶠ χ in 𝓝 ψ,
              sourcePsiSelectedEquationSequence hp hp1 n c R (s χ) χ = 0 := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,_,_,_,_,_,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,hC1,
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n),?_⟩
  intro a ψ hmem hψ hroots hzero hF
  exact exists_analytic_sourcePsi_local_solution_of_analytic
    hp hp1 n c R a ψ hF hzero
      (hbij a ψ hmem.1 hψ hroots hmem.2)

end NLS.ZakharovShabat
