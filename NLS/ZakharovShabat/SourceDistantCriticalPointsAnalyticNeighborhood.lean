import NLS.ZakharovShabat.SourceCriticalSimplicityNeighborhood

/-!
# Uniform source analyticity of distant critical coordinates

A single local canonical labeling makes all distant critical coordinates
continuous at every source in a common complex neighborhood. All critical
roots are simple on a possibly smaller common neighborhood. The analytic
implicit-root theorem then gives source analyticity there for every distant
index, with one cutoff and one neighborhood.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one complex neighborhood of a real-type source, every sufficiently
distant canonical critical point is analytic in the source. -/
theorem exists_local_source_distantCanonicalCriticalPoints_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalCriticalPoints hp hp1 (periodOnePotential χ)
            (periodOnePotential_mem χ) n) ψ := by
  let P : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  obtain ⟨N,_,U,hUopen,_,hφU,_,R,_,hlabel⟩ :=
    exists_uniform_canonicalCriticalPoints hp hp1 (periodOnePotential φ)
  obtain ⟨Vs,hVsopen,hφVs,hsimple⟩ :=
    exists_local_source_allCanonicalCriticalPoints_simple hp hp1 φ hreal
  let V : Set (CoeffPair p) := (periodOnePotential (p := p)) ⁻¹' U ∩ Vs
  have hVopen : IsOpen V :=
    (hUopen.preimage (periodOnePotential (p := p)).continuous).inter hVsopen
  have hφV : φ ∈ V := ⟨hφU,hφVs⟩
  refine ⟨N,V,hVopen,hφV,?_⟩
  intro ψ hψ n hn
  let a : CoeffPair p → ℂ := fun χ =>
    canonicalCriticalPoints hp hp1 (periodOnePotential χ)
      (periodOnePotential_mem χ) n
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1
  have hF : AnalyticAt ℂ F (a ψ,ψ) :=
    (analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1)
      (a ψ,ψ) (mem_univ _)
  have hlabelNear : ∀ᶠ χ : pairParitySubspace (p := p) 0 in 𝓝 (P ψ),
      CriticalPointLabeling hp hp1 χ.val χ.property N
        (canonicalCriticalPoints hp hp1 χ.val χ.property) := by
    have he : ∀ᶠ χ : pairParitySubspace (p := p) 0 in 𝓝 (P ψ), χ.val ∈ U :=
      continuous_subtype_val.continuousAt.eventually (hUopen.mem_nhds hψ.1)
    filter_upwards [he] with χ hχ
    exact (hlabel χ.val hχ χ.property).1
  have ha : ContinuousAt a ψ :=
    (continuousAt_canonicalCriticalPoints_of_eventually_labeling hp hp1
      (P ψ) N n hn hlabelNear).comp P.continuous.continuousAt
  have hroot : ∀ᶠ χ : CoeffPair p in 𝓝 ψ, F (a χ,χ) = 0 :=
    Filter.Eventually.of_forall fun χ =>
      canonicalCriticalPoints_is_critical hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) n
  have hsimpleAt : deriv (deriv (canonicalDiscriminant hp
      (periodOnePotential ψ))) (a ψ) ≠ 0 := hsimple ψ hψ.2 n
  have hsection := deriv_spectral_section_eq_fderiv
    F (a ψ) ψ hF.differentiableAt
  have hsimpleF : (fderiv ℂ F (a ψ,ψ)) (1,0) ≠ 0 := by
    rw [← hsection]
    exact hsimpleAt
  exact analyticAt_implicitRoot F a ψ hF ha hroot hsimpleF

end NLS.ZakharovShabat
