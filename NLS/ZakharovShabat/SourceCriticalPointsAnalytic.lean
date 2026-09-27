import NLS.ComplexAnalysis.AnalyticImplicitRoot
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ZakharovShabat.RealCriticalSimplicity
import NLS.ZakharovShabat.CanonicalCriticalContinuity

/-!
# Analyticity of simple critical coordinates at real-type sources

The discriminant derivative is jointly analytic in spectral parameter
and source. Every real-type critical point is simple and its canonical
label varies continuously. The analytic implicit-zero theorem therefore
upgrades each fixed canonical critical coordinate to an analytic map
of the complex source parameter.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each indexed canonical critical point is analytic in the source
parameter at a real-type potential. -/
theorem analyticAt_sourceCanonicalCriticalPoint_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (fun ψ : CoeffPair p =>
      canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) φ := by
  let a : CoeffPair p → ℂ := fun ψ =>
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1
  have hF : AnalyticAt ℂ F (a φ, φ) :=
    (analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1)
      (a φ, φ) (mem_univ _)
  let P : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  have ha : ContinuousAt a φ := by
    exact (continuousAt_canonicalCriticalPoints_of_realType hp hp1
      (P φ) (isRealType_periodOnePotential φ hreal) n).comp
        P.continuous.continuousAt
  have hroot : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, F (a ψ, ψ) = 0 :=
    Filter.Eventually.of_forall fun ψ =>
      canonicalCriticalPoints_is_critical hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hcrit : F (a φ, φ) = 0 := hroot.self_of_nhds
  have hsimp : deriv (deriv (canonicalDiscriminant hp
      (periodOnePotential φ))) (a φ) ≠ 0 :=
    discriminant_second_derivative_ne_zero_at_critical_of_realType
      hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hreal) (a φ) hcrit
  have hsection := deriv_spectral_section_eq_fderiv
    F (a φ) φ hF.differentiableAt
  have hsimple : (fderiv ℂ F (a φ, φ)) (1, 0) ≠ 0 := by
    rw [← hsection]
    exact hsimp
  exact analyticAt_implicitRoot F a φ hF ha hroot hsimple

end NLS.ZakharovShabat
