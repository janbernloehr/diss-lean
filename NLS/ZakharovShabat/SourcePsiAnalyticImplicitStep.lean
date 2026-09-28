import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import NLS.ZakharovShabat.SourcePsiLocalJacobianBijectivity

/-!
# Analytic implicit step for the selected psi equation

The bounded selected-root Jacobian is precisely the partial
Fréchet derivative of the Banach-valued psi equation. Thus analytic
dependence of any continuous local zero selection follows from the
Banach analytic implicit-zero theorem whenever that Jacobian is
bijective.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected-root Jacobian agrees with the partial derivative of
the joint selected psi equation in its deleted-root variable. -/
theorem sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hF : DifferentiableAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ)) :
    (fderiv ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ)).comp
        (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) =
      sourcePsiSelectedRootJacobian hp hp1 n c R a ψ := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hinc : HasFDerivAt
      (fun b : DeletedCoeff p n => (b,ψ))
      (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) a :=
    hasFDerivAt_prodMk_left a ψ
  have hcomp := hF.hasFDerivAt.comp a hinc
  exact hcomp.fderiv.symm

/-- A continuous local solution selection of the analytic selected
psi equation is analytic wherever its selected-root Jacobian is
bijective. -/
theorem analyticAt_sourcePsi_implicit_solution_of_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (s : CoeffPair p → DeletedCoeff p n) (ψ : CoeffPair p)
    (hF : AnalyticAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (s ψ,ψ))
    (hs : ContinuousAt s ψ)
    (hzero : ∀ᶠ φ in 𝓝 ψ,
      sourcePsiSelectedEquationSequence hp hp1 n c R (s φ) φ = 0)
    (hbij : Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n c R (s ψ) ψ)) :
    AnalyticAt ℂ s ψ := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hpartial := sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian
    hp hp1 n c R (s ψ) ψ hF.differentiableAt
  apply NLS.ComplexAnalysis.analyticAt_implicitBanachRoot
    F s ψ hF hs hzero
  rw [hpartial]
  exact hbij

/-- Joint analyticity and a bijective selected-root Jacobian produce
an analytic local solution branch through a zero of the selected psi
equation. -/
theorem exists_analytic_sourcePsi_local_solution_of_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hF : AnalyticAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ))
    (hzero : sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0)
    (hbij : Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)) :
    ∃ s : CoeffPair p → DeletedCoeff p n,
      AnalyticAt ℂ s ψ ∧ s ψ = a ∧
      ∀ᶠ φ in 𝓝 ψ,
        sourcePsiSelectedEquationSequence hp hp1 n c R (s φ) φ = 0 := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hpartial := sourcePsiSelectedEquation_partial_fderiv_eq_rootJacobian
    hp hp1 n c R a ψ hF.differentiableAt
  apply NLS.ComplexAnalysis.exists_analytic_implicitBanachRoot
    F a ψ hF hzero
  rw [hpartial]
  exact hbij

end NLS.ZakharovShabat
