import NLS.ComplexAnalysis.BanachC1ImplicitRoot
import NLS.ZakharovShabat.SourcePsiAnalyticImplicitStep
import NLS.ZakharovShabat.SourcePsiRootPlacementDomain

/-!
# Local `C¹` implicit branches for the selected psi equation

The selected equation is `C¹` on the same local contour family on
which its root Jacobian is bijective at real solutions. Thus every
such zero extends to a local `C¹` zero branch without an additional
analyticity hypothesis.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- A zero of the `C¹` selected psi equation with bijective root
Jacobian extends to a local `C¹` zero branch. -/
theorem exists_C1_sourcePsi_local_solution
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hF : ContDiffAt ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ))
    (hzero : sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0)
    (hbij : Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      ContDiffAt ℂ 1 s ψ ∧ s ψ = a ∧
      ∀ᶠ χ in 𝓝 ψ,
        sourcePsiSelectedEquationSequence hp hp1 n c R (s χ) χ = 0 := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hpartial := sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian
    hp hp1 n c R a ψ (hF.differentiableAt (by norm_num))
  apply NLS.ComplexAnalysis.exists_C1_implicitBanachRoot
    F a ψ hF hzero
  rw [hpartial]
  exact hbij

/-- Near a real-type source, one selected contour family gives a
`C¹` equation and a `C¹` local solution branch through every real
zero whose retained roots lie in the open placement domain. -/
theorem exists_local_sourcePsi_C1_branch
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
          ∃ s : CoeffPair p → DeletedCoeff p n,
            ContDiffAt ℂ 1 s ψ ∧ s ψ = a ∧
            ∀ᶠ χ in 𝓝 ψ,
              (s χ,χ) ∈ U ∩
                sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n ∧
              sourcePsiSelectedEquationSequence hp hp1 n c R (s χ) χ = 0 := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,_,_,_,_,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective hp hp1 φ hφ n a₀
  have hDopen : IsOpen (U ∩
      sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n) :=
    hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n)
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,hC1,
    hDopen,?_⟩
  intro a ψ hmem hψ hroots hzero
  have hF : ContDiffAt ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ) := hC1.contDiffAt (hUopen.mem_nhds hmem.1)
  obtain ⟨s,hs,hsx,hzeros⟩ := exists_C1_sourcePsi_local_solution
    hp hp1 n c R a ψ hF hzero
      (hbij a ψ hmem.1 hψ hroots hmem.2)
  have hcontinuous : ContinuousAt
      (fun χ : CoeffPair p => (s χ,χ)) ψ :=
    hs.continuousAt.prodMk continuousAt_id
  have hplacement : ∀ᶠ χ in 𝓝 ψ,
      (s χ,χ) ∈ U ∩
        sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n := by
    apply hcontinuous.eventually
    apply hDopen.mem_nhds
    simpa only [hsx] using hmem
  refine ⟨s,hs,hsx,?_⟩
  filter_upwards [hplacement,hzeros] with χ hχ hχzero
  exact ⟨hχ,hχzero⟩

end NLS.ZakharovShabat
