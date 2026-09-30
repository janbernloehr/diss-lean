import NLS.ZakharovShabat.SourceAngularCosineLift
import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence

/-!
# Local analytic diagonal eta representatives on the cosine cover

The actual diagonal psi numerator defines the endpoint-normalized eta
primitive on the cosine cover. Its value is the integral of the literal
pulled-back angular differential on every regular interior angle path,
also with a singular endpoint. The actual terminal-angle construction
makes this representative source analytic near every open real gap.
Identification and gluing of all admissible spectral paths modulo pi
remain separate parts of Theorem 13.1(ii).
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual diagonal angular primitive on a terminal-normalized
cosine lift, with its zero normalization at the left-endpoint angle pi. -/
def sourceAngularEtaCosineRepresentative (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ : ℂ) : ℂ × CoeffPair p → ℂ :=
  fun x => (-κ * Complex.I) * sourceAngularCanonicalCosinePrimitive hp hp1 n n s x

@[simp] theorem sourceAngularEtaCosineRepresentative_pi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (κ : ℂ) (ψ : CoeffPair p) :
    sourceAngularEtaCosineRepresentative hp hp1 n s κ ((Real.pi : ℂ),ψ) = 0 := by
  simp only [sourceAngularEtaCosineRepresentative,sourceAngularCanonicalCosinePrimitive_pi,mul_zero]

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- The diagonal representative is jointly analytic in angle and
source throughout the actual canonical cosine chart. -/
theorem analyticOnNhd_etaCosineRepresentative
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R) (κ : ℂ) :
    AnalyticOnNhd ℂ (sourceAngularEtaCosineRepresentative hp hp1 m s κ) (Ω ×ˢ V) :=
  fun x hx => analyticAt_const.mul (D.primitive_analytic m x hx)

/-- The literal psi/root pullback is integrable and evaluates to the
actual diagonal representative along any C1 angle path from pi whose
interior avoids sine zeros. Singular terminal endpoints are allowed. -/
theorem etaCosineRepresentative_eq_lifted_pathIntegral
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (e κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (γ : Path (Real.pi : ℂ) e) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hγΩ : ∀ t : unitInterval, γ t ∈ Ω)
    (hsin : ∀ t ∈ Ioo (0 : ℝ) 1, Complex.sin (γ.extend t) ≠ 0) :
    CurveIntegrable (holomorphicOneForm (fun θ =>
      sourceAngularCosineLiftedIntegrand hp hp1 m m s κ (θ,ψ))) γ ∧
      (∫ᶜ θ in γ, holomorphicOneForm (fun θ =>
        sourceAngularCosineLiftedIntegrand hp hp1 m m s κ (θ,ψ)) θ) =
          sourceAngularEtaCosineRepresentative hp hp1 m s κ (e,ψ) := by
  let f : ℂ → ℂ := fun θ => sourceAngularCosineLiftedIntegrand hp hp1 m m s κ (θ,ψ)
  let g : ℂ → ℂ := fun θ => (-κ * Complex.I) * sourceAngularGapNumerator hp hp1 m m s ψ
    (sourceCanonicalCosinePoint hp hp1 m (θ,ψ))
  let F : ℂ → ℂ := fun θ => sourceAngularEtaCosineRepresentative hp hp1 m s κ (θ,ψ)
  have hg : AnalyticOnNhd ℂ g Ω := by
    intro θ hθ
    exact analyticAt_const.mul ((D.numerator_analytic m (θ,ψ) ⟨hθ,hψ⟩).comp
      (f := fun θ : ℂ => (θ,ψ)) (analyticAt_id.prod analyticAt_const))
  have hγs : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ Ω := by
    intro t ht
    simpa only [Path.extend_apply γ ht] using hγΩ ⟨t,ht⟩
  have hint : CurveIntegrable (holomorphicOneForm g) γ :=
    (hg.continuousOn.smul continuousOn_const).curveIntegrable_of_contDiffOn hγ hγΩ
  have heq : ∀ t ∈ Ioo (0 : ℝ) 1, f (γ.extend t) = g (γ.extend t) :=
    fun t ht => D.cosineLiftedIntegrand_eq_gapNumerator ψ hψ m (γ.extend t)
      (hγs t (Ioo_subset_Icc_self ht)) (hsin t ht) κ hκ
  have hF : ∀ θ ∈ Ω, HasDerivAt F (g θ) θ := fun θ hθ =>
    (D.primitive_derivative m ψ hψ θ hθ).const_mul (-κ * Complex.I)
  refine ⟨(curveIntegrable_holomorphicOneForm_congr_interior f g γ heq).mpr hint,?_⟩
  change (∫ᶜ θ in γ, holomorphicOneForm f θ) = F e
  rw [curveIntegral_holomorphicOneForm_congr_interior f g γ heq,
    curveIntegral_eq_sub_of_primitive g F Ω hF γ hγ hγs hint]
  simp only [F,sourceAngularEtaCosineRepresentative_pi,sub_zero]

/-- Near every open real gap, including either periodic terminal,
the actual terminal-normalized diagonal primitive has an analytic
source representative on a constructed open neighborhood. -/
theorem exists_local_analytic_real_eta_cosine_representative
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ ε : CoeffPair p → ℂ, ∃ κ : ℂ, (κ = 1 ∨ κ = -1) ∧ AnalyticOnNhd ℂ ε U ∧
        ε φ ∈ segment ℝ (0 : ℂ) (Real.pi : ℂ) ∧
        (∀ ψ ∈ U, ε ψ ∈ Ω ∧
          sourceCanonicalCosinePoint hp hp1 m (ε ψ,ψ) = canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∧
          Complex.sin (ε ψ) = κ * sourceAngularDirichletSine hp hp1 m ψ ∧
          sourceAngularCosineLiftedRoot hp hp1 m κ (ε ψ,ψ) =
            sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)) ∧
        AnalyticOnNhd ℂ (fun ψ => sourceAngularEtaCosineRepresentative hp hp1 m s κ (ε ψ,ψ)) U := by
  obtain ⟨U,hU,hφU,hUV,ε,κ,hκ,hε,he,hzeros⟩ := D.exists_local_analytic_real_dirichlet_angle φ hφ hreal
  refine ⟨U,hU,hφU,hUV,ε,κ,hκ,hε,he,?_,?_⟩
  · intro ψ hψ
    obtain ⟨hangle,hpoint,hsin⟩ := hzeros ψ hψ
    exact ⟨hangle,hpoint,hsin,D.cosineLiftedRoot_eq_dirichlet_anti ψ (hUV hψ) (ε ψ) κ hκ hpoint hsin⟩
  · intro ψ hψ
    exact (D.analyticOnNhd_etaCosineRepresentative κ (ε ψ,ψ)
      ⟨(hzeros ψ hψ).1,hUV hψ⟩).comp (f := fun ψ : CoeffPair p => (ε ψ,ψ))
      ((hε ψ hψ).prod analyticAt_id)

end SourceAngularCanonicalCosineChartData
end NLS.ZakharovShabat
