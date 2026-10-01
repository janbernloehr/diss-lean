import NLS.ZakharovShabat.SourceOmittedRootIsospectral
import NLS.ZakharovShabat.SourcePsiIsospectralRoots
import NLS.ZakharovShabat.SourceAngularEndpointBound

/-! # Stationarity of the actual angular integrands

The normalized psi numerator and the actual spectral denominator are
stationary in isospectral directions. This proves zero variation of
the canonical angular integrand and of its regular gap numerator,
the latter even at the selected periodic endpoints.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem stationary_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F Q : E → ℂ) (a h : E) (hF : DifferentiableAt ℂ F a)
    (hQ : DifferentiableAt ℂ Q a) (hne : Q a ≠ 0)
    (hFzero : (fderiv ℂ F a) h = 0) (hQzero : (fderiv ℂ Q a) h = 0) :
    (fderiv ℂ (fun b => F b/Q b) a) h = 0 := by
  have hi := (hasFDerivAt_inv hne).comp a hQ.hasFDerivAt
  have hd := hF.hasFDerivAt.fun_mul hi
  simp only [Function.comp_def] at hd
  simp only [div_eq_mul_inv]
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply,hFzero,hQzero]

namespace SourcePsiIsolatingComplexExtension
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual canonical angular integrand has zero source variation
in every isospectral direction off the periodic cuts. -/
theorem fderiv_angularIntegrand_isospectral_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceAngularIntegrand n s
      (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) φ.val) h = 0 := by
  have hN : DifferentiableAt ℂ (fun ψ : CoeffPair p =>
      sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ.val :=
    ((hs.analytic_numerator_joint n (z,φ.val) ⟨mem_univ _,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  obtain ⟨V,_,_,hVreal,_,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  have hQ : DifferentiableAt ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ.val := by
    simpa only [Function.comp_def] using! ((hroot (z,φ.val) ⟨hVreal φ.property,hz⟩).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact stationary_quotient _ _ φ.val h hN hQ
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ.val z hz)
    (hs.fderiv_numerator_isospectral_eq_zero n φ hφ h hiso z)
    (fderiv_sourceCanonicalRoot_eq_zero_of_isospectralDirection hp hp1 φ.val φ.property h hiso z hz)

/-- The actual regular gap numerator is stationary on the entire
omitted-root domain, including the selected gap and both endpoints. -/
theorem fderiv_angularGapNumerator_isospectral_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (n m : ℤ) (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h)
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceAngularGapNumerator hp hp1 n m s ψ z) φ.val) h = 0 := by
  have hN : DifferentiableAt ℂ (fun ψ : CoeffPair p =>
      sourcePsiCandidate n (z,(s n ψ : Coeff p))) φ.val :=
    ((hs.analytic_numerator_joint n (z,φ.val) ⟨mem_univ _,hφ⟩).comp
      (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  obtain ⟨V,_,_,hVreal,hroot⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hP : DifferentiableAt ℂ
      (fun ψ : CoeffPair p => sourceStandardRootOmittedProduct hp hp1 m ψ z) φ.val := by
    simpa only [sourceStandardRootOmittedJointProduct,Function.comp_def] using!
      (((hroot m).2.1 (z,φ.val) ⟨hVreal φ.property,hz⟩).comp
        (f := fun ψ : CoeffPair p => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hQ : DifferentiableAt ℂ
      (fun ψ : CoeffPair p => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z) φ.val :=
    (differentiableAt_const (2*I)).fun_mul hP
  have hQzero : (fderiv ℂ
      (fun ψ : CoeffPair p => 2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z) φ.val) h = 0 := by
    rw [fderiv_const_mul hP]
    simp only [smul_apply,smul_eq_mul]
    rw [fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m z hz,mul_zero]
  exact stationary_quotient _ _ φ.val h hN hQ
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 φ.val z m hz))
    (hs.fderiv_numerator_isospectral_eq_zero n φ hφ h hiso z) hQzero

/-- The actual canonical angular integrand commutes with every
actual action at every fixed spectral parameter off the cuts. -/
theorem sourceBracket_angularIntegrand_action_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAngularIntegrand n s
      (sourceCanonicalRootJointProduct hp hp1) (z,ψ)) (sourceComplexAction hp hp1 m) φ.val = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact hs.fderiv_angularIntegrand_isospectral_eq_zero n φ hφ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property m) z hz

/-- Every actual regular angular gap numerator commutes with every
actual action throughout its full omitted-root domain. -/
theorem sourceBracket_angularGapNumerator_action_eq_zero
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k m : ℤ)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W)
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ.val k) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAngularGapNumerator hp hp1 n k s ψ z)
      (sourceComplexAction hp hp1 m) φ.val = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact hs.fderiv_angularGapNumerator_isospectral_eq_zero n k φ hφ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property m) z hz

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
