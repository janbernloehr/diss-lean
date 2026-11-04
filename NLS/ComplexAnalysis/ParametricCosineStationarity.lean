import NLS.ComplexAnalysis.IntegralSourceStationarity
import NLS.ComplexAnalysis.ParametricCosinePrimitive
import NLS.ComplexAnalysis.ImplicitRootStationarity

/-! # Source stationarity of the actual normalized cosine primitive -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Stationary midpoint, half-length and filled numerator give a stationary
literal affine-segment primitive in the cosine coordinate. -/
theorem fderiv_parametricCosinePrimitive_source_apply_eq_zero
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (D : Set (ℂ × A)) (Ω : Set ℂ) (V : Set A)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hπ : (Real.pi : ℂ)∈Ω)
    (hg : AnalyticOnNhd ℂ g D) (hτ : AnalyticOnNhd ℂ τ V) (hδ : AnalyticOnNhd ℂ δ V)
    (hchart : ∀ x∈Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)∈D)
    (a v : A) (ha : a∈V)
    (hτzero : (fderiv ℂ τ a) v=0) (hδzero : (fderiv ℂ δ a) v=0)
    (hgzero : ∀ z : ℂ, (z,a)∈D → (fderiv ℂ (fun p : A => g (z,p)) a) v=0)
    (θ : ℂ) (hθ : θ∈Ω) :
    (fderiv ℂ (fun p : A => parametricCosinePrimitive g τ δ (θ,p)) a) v=0 := by
  have hnum := analyticOnNhd_parametricCosineNumerator g τ δ D Ω V hg hτ hδ hchart
  apply fderiv_parametricConvexPrimitive_source_apply_eq_zero
    (parametricCosineNumerator g τ δ) Ω V Real.pi hΩ hconv hV hπ hnum a v ha _ θ hθ
  intro e he
  let L (p : A) := cosineGapPoint (τ p) (δ p) e
  have hL : AnalyticAt ℂ L a := (hτ a ha).add ((hδ a ha).mul analyticAt_const)
  let H (u : ℂ × ℂ) := cosineGapPoint u.1 u.2 e
  have hH : AnalyticAt ℂ H (τ a,δ a) := analyticAt_fst.add (analyticAt_snd.mul analyticAt_const)
  have hd := congrArg (fun T : A →L[ℂ] ℂ => T v)
    (hH.differentiableAt.hasFDerivAt.comp a
      ((hτ a ha).differentiableAt.hasFDerivAt.prodMk (hδ a ha).differentiableAt.hasFDerivAt)).fderiv
  change (fderiv ℂ L a) v=(fderiv ℂ H (τ a,δ a)) ((fderiv ℂ τ a) v,(fderiv ℂ δ a) v) at hd
  rw [hτzero,hδzero] at hd
  change (fderiv ℂ L a) v=(fderiv ℂ H (τ a,δ a)) (0 : ℂ × ℂ) at hd
  rw [map_zero] at hd
  have hcomp := fderiv_pair_comp_apply_of_left_eq_zero g L a v
    (hg _ (hchart (e,a) ⟨he,ha⟩)).differentiableAt hL.differentiableAt hd
  exact hcomp.trans (hgzero _ (hchart (e,a) ⟨he,ha⟩))

/-- A moving terminal contributes only its spectral chain rule when the
actual source section of the joint family is stationary. -/
theorem fderiv_moving_terminal_apply_of_source_eq_zero
    (F : ℂ × A → ℂ) (μ : A → ℂ) (a v : A)
    (hF : DifferentiableAt ℂ F (μ a,a)) (hμ : DifferentiableAt ℂ μ a)
    (hz : (fderiv ℂ (fun p : A => F (μ a,p)) a) v=0) :
    (fderiv ℂ (fun p : A => F (μ p,p)) a) v=
      deriv (fun z : ℂ => F (z,a)) (μ a)*((fderiv ℂ μ a) v) := by
  have hd := congrArg (fun T : A →L[ℂ] ℂ => T v)
    (hF.hasFDerivAt.comp a (f := fun p : A => (μ p,p))
      (hμ.hasFDerivAt.prodMk (hasFDerivAt_id a))).fderiv
  change (fderiv ℂ (fun p : A => F (μ p,p)) a) v=
    (fderiv ℂ F (μ a,a)) ((fderiv ℂ μ a) v,v) at hd
  have hs := congrArg (fun T : A →L[ℂ] ℂ => T v) (fderiv_source_section_eq_joint F (μ a) a hF)
  change (fderiv ℂ (fun p : A => F (μ a,p)) a) v=(fderiv ℂ F (μ a,a)) (0,v) at hs
  rw [hz] at hs
  have he : ((fderiv ℂ μ a) v,v)=((fderiv ℂ μ a) v) • ((1 : ℂ),(0 : A))+(0,v) := by simp
  rw [he,map_add,map_smul,← hs,add_zero,smul_eq_mul,
    ← deriv_spectral_section_eq_fderiv F (μ a) a hF] at hd
  exact hd.trans (mul_comm _ _)

end NLS.ComplexAnalysis
