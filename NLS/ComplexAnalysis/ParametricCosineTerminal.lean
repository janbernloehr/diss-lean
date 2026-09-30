import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import NLS.ComplexAnalysis.ParametricCosineChart

/-!
# Analytic moving terminals in cosine coordinates

At a noncritical angle an analytic moving spectral terminal has an
analytic local cosine coordinate. The analytic implicit function theorem
constructs the coordinate and its exact equation on a source neighborhood.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]

/-- An analytic terminal has an analytic cosine angle near any regular
base angle. Neither a preselected moving angle nor its continuity is input. -/
theorem exists_analytic_parametricCosine_terminal
    (τ δ μ : A → ℂ) (a : A) (e : ℂ)
    (hτ : AnalyticAt ℂ τ a) (hδ : AnalyticAt ℂ δ a) (hμ : AnalyticAt ℂ μ a)
    (hδne : δ a ≠ 0) (hsin : Complex.sin e ≠ 0)
    (hpoint : cosineGapPoint (τ a) (δ a) e = μ a) :
    ∃ ε : A → ℂ, AnalyticAt ℂ ε a ∧ ε a = e ∧
      ∀ᶠ b in 𝓝 a, cosineGapPoint (τ b) (δ b) (ε b) = μ b := by
  let F : ℂ × A → ℂ := fun x => cosineGapPoint (τ x.2) (δ x.2) x.1-μ x.2
  have hF : AnalyticAt ℂ F (e,a) := by
    exact ((hτ.comp (f := fun x : ℂ × A => x.2) analyticAt_snd).add
      ((hδ.comp (f := fun x : ℂ × A => x.2) analyticAt_snd).mul
        (Complex.analyticAt_cos.comp (f := fun x : ℂ × A => x.1) analyticAt_fst))).sub
      (hμ.comp (f := fun x : ℂ × A => x.2) analyticAt_snd)
  have hderiv : HasDerivAt (fun θ => F (θ,a)) (-δ a*Complex.sin e) e :=
    (hasDerivAt_cosineGapPoint (τ a) (δ a) e).sub_const (μ a)
  have hfull : HasFDerivAt F (fderiv ℂ F (e,a)) (e,a) := hF.differentiableAt.hasFDerivAt
  have hgraph : HasFDerivAt (fun θ : ℂ => (θ,a)) (ContinuousLinearMap.inl ℂ ℂ A) e :=
    hasFDerivAt_prodMk_left e a
  have hpartial : (fderiv ℂ F (e,a)).comp (ContinuousLinearMap.inl ℂ ℂ A) =
      ContinuousLinearMap.toSpanSingleton ℂ (-δ a*Complex.sin e) := by
    have hc : HasFDerivAt (fun θ => F (θ,a))
        ((fderiv ℂ F (e,a)).comp (ContinuousLinearMap.inl ℂ ℂ A)) e :=
      hfull.comp (f := fun θ : ℂ => (θ,a)) e hgraph
    exact hc.unique hderiv.hasFDerivAt
  have hdne : -δ a*Complex.sin e ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hδne) hsin
  have hbij : Function.Bijective
      ((fderiv ℂ F (e,a)).comp (ContinuousLinearMap.inl ℂ ℂ A)) := by
    rw [hpartial]
    constructor
    · intro x y hxy
      exact mul_right_cancel₀ hdne (by simpa using hxy)
    · intro z
      refine ⟨z/(-δ a*Complex.sin e),?_⟩
      change (z/(-δ a*Complex.sin e))*(-δ a*Complex.sin e) = z
      exact div_mul_cancel₀ z hdne
  obtain ⟨ε,hε,hεa,hzeros⟩ := exists_analytic_implicitBanachRoot F e a hF
    (sub_eq_zero.mpr hpoint) hbij
  exact ⟨ε,hε,hεa,hzeros.mono fun _ h => sub_eq_zero.mp h⟩

end NLS.ComplexAnalysis
