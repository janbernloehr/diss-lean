import NLS.ZakharovShabat.SourceDistantCriticalPointsAnalyticNeighborhood

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
theorem exists_local_source_distantCanonicalCriticalPoints_analytic_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), 0 < N ∧ IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N < n.natAbs →
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalCriticalPoints hp hp1 (periodOnePotential χ)
            (periodOnePotential_mem χ) n) ψ ∧
        deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ)))
          (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n) ≠ 0 := by
  let P : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  obtain ⟨N,hN,U,hUopen,_,hφU,_,R,_,hlabel⟩ :=
    exists_uniform_canonicalCriticalPoints hp hp1 (periodOnePotential φ)
  let V := (periodOnePotential (p := p)) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (periodOnePotential (p := p)).continuous
  refine ⟨N,V,hN,hVopen,hφU,?_⟩
  intro ψ hψ n hn
  let a : CoeffPair p → ℂ := fun χ =>
    canonicalCriticalPoints hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1
  have hF : AnalyticAt ℂ F (a ψ,ψ) :=
    analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1 (a ψ,ψ) (mem_univ _)
  have hlabelNear : ∀ᶠ χ : pairParitySubspace (p := p) 0 in 𝓝 (P ψ),
      CriticalPointLabeling hp hp1 χ.val χ.property N
        (canonicalCriticalPoints hp hp1 χ.val χ.property) := by
    have he : ∀ᶠ χ : pairParitySubspace (p := p) 0 in 𝓝 (P ψ), χ.val ∈ U :=
      continuous_subtype_val.continuousAt.eventually (hUopen.mem_nhds hψ)
    filter_upwards [he] with χ hχ
    exact (hlabel χ.val hχ χ.property).1
  have ha : ContinuousAt a ψ :=
    (continuousAt_canonicalCriticalPoints_of_eventually_labeling hp hp1
      (P ψ) N n hn hlabelNear).comp P.continuous.continuousAt
  have hroot : ∀ᶠ χ : CoeffPair p in 𝓝 ψ, F (a χ,χ) = 0 :=
    Filter.Eventually.of_forall fun χ =>
      canonicalCriticalPoints_is_critical hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n
  have horder := ((hlabel _ hψ (periodOnePotential_mem ψ)).1.distant n hn).2.2.1
  have hanalytic := analyticOnNhd_discriminant_derivative hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) (a ψ) (mem_univ _)
  have hderivOrder : analyticOrderAt (deriv (deriv (canonicalDiscriminant hp
      (periodOnePotential ψ)))) (a ψ) = 0 :=
    analyticOrderAt_deriv_of_pos hanalytic (n := 0) (by simpa only [a] using! horder)
  have hsimple : deriv (deriv (canonicalDiscriminant hp (periodOnePotential ψ))) (a ψ) ≠ 0 := by
    intro hzero
    exact (hanalytic.deriv.analyticOrderAt_ne_zero.mpr hzero) hderivOrder
  refine ⟨?_,hsimple⟩
  apply analyticAt_implicitRoot F a ψ hF ha hroot
  rw [← deriv_spectral_section_eq_fderiv F (a ψ) ψ hF.differentiableAt]
  exact hsimple


end NLS.ZakharovShabat
