import NLS.ComplexAnalysis.ParametricCosinePrimitive
import NLS.ComplexAnalysis.PrimitiveSourceStationarity
import NLS.ComplexAnalysis.ImplicitRootIsospectralDerivative

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem parametricCosineNumerator_source_fderiv_eq_zero
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (p h : A) (θ : ℂ)
    (hg : AnalyticAt ℂ g (cosineGapPoint (τ p) (δ p) θ,p))
    (hτ : AnalyticAt ℂ τ p) (hδ : AnalyticAt ℂ δ p)
    (hτzero : (fderiv ℂ τ p) h=0) (hδzero : (fderiv ℂ δ p) h=0)
    (hgzero : (fderiv ℂ (fun b : A => g (cosineGapPoint (τ p) (δ p) θ,b)) p) h=0) :
    (fderiv ℂ (fun b : A => parametricCosineNumerator g τ δ (θ,b)) p) h=0 := by
  let a : A → ℂ := fun b => cosineGapPoint (τ b) (δ b) θ
  have ha : AnalyticAt ℂ a p := hτ.add (hδ.mul analyticAt_const)
  have hd := hτ.differentiableAt.hasFDerivAt.fun_add (hδ.differentiableAt.hasFDerivAt.mul_const (Complex.cos θ))
  change HasFDerivAt (𝕜 := ℂ) a _ p at hd
  have hazero : (fderiv ℂ a p) h=0 := by
    rw [hd.fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul,hτzero,hδzero,mul_zero,add_zero]
  change (fderiv ℂ (fun b : A => g (a b,b)) p) h=0
  rw [joint_fderiv_eq_parameter_of_state_kernel g a p h hg ha hazero]
  exact hgzero

/-- The genuine cosine primitive is stationary with its normalized
anchor, including angles corresponding to the periodic endpoints. -/
theorem parametricCosinePrimitive_source_fderiv_eq_zero
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (D : Set (ℂ × A))
    (Ω : Set ℂ) (V : Set A) (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω)
    (hV : IsOpen V) (hπ : (Real.pi : ℂ)∈Ω)
    (hg : AnalyticOnNhd ℂ g D) (hτ : AnalyticOnNhd ℂ τ V) (hδ : AnalyticOnNhd ℂ δ V)
    (hchart : ∀ x∈Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)∈D)
    (p h : A) (hp : p∈V) (hτzero : (fderiv ℂ τ p) h=0) (hδzero : (fderiv ℂ δ p) h=0)
    (hgzero : ∀ θ∈Ω, (fderiv ℂ (fun b : A => g (cosineGapPoint (τ p) (δ p) θ,b)) p) h=0)
    (θ : ℂ) (hθ : θ∈Ω) :
    (fderiv ℂ (fun b : A => parametricCosinePrimitive g τ δ (θ,b)) p) h=0 := by
  apply parametricConvexPrimitive_source_fderiv_eq_zero (parametricCosineNumerator g τ δ) Ω V
    (Real.pi : ℂ) hΩ hconv hV hπ (analyticOnNhd_parametricCosineNumerator g τ δ D Ω V hg hτ hδ hchart) p h hp ?_ θ hθ
  intro e he
  exact parametricCosineNumerator_source_fderiv_eq_zero g τ δ p h e
    (hg _ (hchart (e,p) ⟨he,hp⟩)) (hτ p hp) (hδ p hp) hτzero hδzero (hgzero e he)

end NLS.ComplexAnalysis
