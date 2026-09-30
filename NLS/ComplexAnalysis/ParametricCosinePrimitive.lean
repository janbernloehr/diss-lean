import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.CosinePrimitiveEndpointAgreement

/-!
# Source-dependent normalized cosine primitives

The selected square root disappears after the cosine substitution. Integrate
the remaining jointly analytic numerator from the fixed angle pi. The result
is jointly analytic and agrees, with the exact sheet coefficient, with every
endpoint-normalized spectral primitive on their common angle chart.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Pull back the regular numerator to the cosine coordinate. -/
def parametricCosineNumerator (g : ℂ × A → ℂ) (τ δ : A → ℂ) : ℂ × A → ℂ :=
  fun x => g (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)

/-- Normalize the cosine primitive at the fixed left-endpoint angle pi. -/
def parametricCosinePrimitive (g : ℂ × A → ℂ) (τ δ : A → ℂ) : ℂ × A → ℂ :=
  parametricConvexPrimitive (parametricCosineNumerator g τ δ) (Real.pi:ℂ)

theorem analyticOnNhd_parametricCosineNumerator
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (D : Set (ℂ × A))
    (Ω : Set ℂ) (V : Set A)
    (hg : AnalyticOnNhd ℂ g D) (hτ : AnalyticOnNhd ℂ τ V) (hδ : AnalyticOnNhd ℂ δ V)
    (hchart : ∀ x ∈ Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2) ∈ D) :
    AnalyticOnNhd ℂ (parametricCosineNumerator g τ δ) (Ω ×ˢ V) := by
  intro x hx
  have ht := (hτ x.2 hx.2).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
  have hd := (hδ x.2 hx.2).comp (f := fun x : ℂ × A => x.2) analyticAt_snd
  have hT : AnalyticAt ℂ (fun x : ℂ × A =>
      (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)) x :=
    (ht.add (hd.mul (Complex.analyticAt_cos.comp (f := fun x : ℂ × A => x.1)
      analyticAt_fst))).prod analyticAt_snd
  exact (hg _ (hchart x hx)).comp (x := x)
    (f := fun x : ℂ × A => (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2)) hT

/-- The angle/source primitive is jointly analytic with exact zero
normalization and the prescribed spectral derivative. -/
theorem parametricCosinePrimitive_spec
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (D : Set (ℂ × A))
    (Ω : Set ℂ) (V : Set A) (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω)
    (hV : IsOpen V) (hπ : (Real.pi:ℂ) ∈ Ω)
    (hg : AnalyticOnNhd ℂ g D) (hτ : AnalyticOnNhd ℂ τ V) (hδ : AnalyticOnNhd ℂ δ V)
    (hchart : ∀ x ∈ Ω ×ˢ V, (cosineGapPoint (τ x.2) (δ x.2) x.1,x.2) ∈ D) :
    AnalyticOnNhd ℂ (parametricCosinePrimitive g τ δ) (Ω ×ˢ V) ∧
      (∀ a : A, parametricCosinePrimitive g τ δ ((Real.pi:ℂ),a) = 0) ∧
      ∀ a ∈ V, ∀ θ ∈ Ω, HasDerivAt (fun e => parametricCosinePrimitive g τ δ (e,a))
        (g (cosineGapPoint (τ a) (δ a) θ,a)) θ := by
  have hnum := analyticOnNhd_parametricCosineNumerator g τ δ D Ω V hg hτ hδ hchart
  exact ⟨analyticOnNhd_parametricConvexPrimitive _ Ω V _ hΩ hconv hV hπ hnum,
    fun a => parametricConvexPrimitive_anchor _ _ a,
    fun a ha θ hθ => hasDerivAt_parametricConvexPrimitive _ Ω V _ hΩ hconv hπ hnum a ha θ hθ⟩

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- On a common angle chart the explicit source-dependent primitive equals
the normalized pullback of any canonical spectral primitive, including the
exact selected-root sheet coefficient. No source regularity of the given
spectral primitive is assumed. -/
theorem exists_parametricCosinePrimitive_spectral_matching
    (g : ℂ × A → ℂ) (τ δ : A → ℂ) (a : A)
    (Ω Λ : Set ℂ) (Q F : ℂ → ℂ) (B : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hπ : (Real.pi:ℂ) ∈ Ω)
    (hnum : AnalyticOnNhd ℂ (fun θ => parametricCosineNumerator g τ δ (θ,a)) Ω)
    (hΛ : IsOpen Λ) (hd : δ a ≠ 0)
    (hgap : segment ℝ (τ a-δ a) (τ a+δ a) ⊆ Λ)
    (hg : AnalyticOnNhd ℂ (fun z => g (z,a)) Λ)
    (hQ : ContinuousOn Q (Λ \ segment ℝ (τ a-δ a) (τ a+δ a)))
    (hsq : ∀ z ∈ Λ \ segment ℝ (τ a-δ a) (τ a+δ a),
      Q z^2 = (τ a-δ a-z)*(τ a+δ a-z))
    (hF : ∀ z ∈ Λ \ segment ℝ (τ a-δ a) (τ a+δ a), HasDerivAt F (g (z,a)/Q z) z)
    (hB : Tendsto F (𝓝[Λ \ segment ℝ (τ a-δ a) (τ a+δ a)] (τ a-δ a)) (𝓝 B)) :
    ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ (Real.pi:ℂ) ∈ U ∧ U ⊆ Ω ∧
      ∀ θ ∈ U, θ.im ≠ 0 → F (cosineGapPoint (τ a) (δ a) θ)-B =
        cosineRootCoefficient Q (τ a) (δ a) θ * parametricCosinePrimitive g τ δ (θ,a) := by
  obtain ⟨S,H,hS,hSconv,hseg,hT,hH,hmatch⟩ := exists_cosine_gap_primitive_chart
    (fun z => g (z,a)) Q F Λ (τ a) (δ a) B hΛ hd hgap hg hQ hsq hF hB
  have hπS : (Real.pi:ℂ) ∈ S := hseg (right_mem_segment ℝ _ _)
  refine ⟨Ω ∩ S,hΩ.inter hS,hconv.inter hSconv,⟨hπ,hπS⟩,inter_subset_left,?_⟩
  intro θ hθ hi
  have heq : parametricCosinePrimitive g τ δ (θ,a) = H θ-H (Real.pi:ℂ) :=
    parametricConvexPrimitive_eq_sub_of_primitive _ (Ω ∩ S) _ a (hconv.inter hSconv)
      ⟨hπ,hπS⟩ (hnum.continuousOn.mono inter_subset_left) H
      (fun e he => hH e he.2) θ hθ
  rw [heq]
  exact hmatch θ hθ.2 hi

end NLS.ComplexAnalysis
