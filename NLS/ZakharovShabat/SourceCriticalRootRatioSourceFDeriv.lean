import NLS.ComplexAnalysis.QuotientDerivative
import NLS.ZakharovShabat.SourceCanonicalRootSourceFDeriv
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ZakharovShabat.SourceDiscriminantMixedDerivative

/-!
# Source derivative of the critical-root quotient

The source derivative of the action's unweighted integrand
`Δ' / Q` is expanded using the canonical-root square identity.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source Fréchet derivative of the critical-root quotient at a
real-type source, away from all moving periodic cuts. -/
theorem fderiv_sourceCriticalRootRatioJoint_source
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h =
      ((fderiv ℂ (fun ψ : CoeffPair p =>
          deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z) φ) h *
          sourceCanonicalRoot hp hp1 φ z -
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) z *
          (canonicalDiscriminant hp (periodOnePotential φ) z /
            sourceCanonicalRoot hp hp1 φ z *
            (fderiv ℂ (fun ψ : CoeffPair p =>
              canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h)) /
        (sourceCanonicalRoot hp hp1 φ z)^2 := by
  let N : CoeffPair p → ℂ := fun ψ =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z
  let Q : CoeffPair p → ℂ := fun ψ => sourceCanonicalRoot hp hp1 ψ z
  have hN : DifferentiableAt ℂ N φ := by
    have hjoint := analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1
    exact ((hjoint (z,φ) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hQ : DifferentiableAt ℂ Q φ := by
    obtain ⟨W,_,_,hreal,_,hroot⟩ :=
      exists_global_source_analytic_canonicalRoot hp hp1
    have hpoint : (z,φ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
      ⟨hreal hφ,hz⟩
    exact ((hroot (z,φ) hpoint).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hquot := NLS.ComplexAnalysis.fderiv_div_apply N Q φ hN hQ
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz) h
  rw [fderiv_sourceCanonicalRoot_eq_discriminant_div_root_mul_fderiv
    hp hp1 φ hφ z hz h] at hquot
  exact hquot

/-- The source derivative of `Δ' / Q` is a spectral derivative:
`∂₍φ₎(Δ' / Q) = ∂₍z₎((∂₍φ₎Δ) / Q)`. This is the pointwise
identity needed for the action contour integration by parts. -/
theorem fderiv_sourceCriticalRootRatioJoint_eq_deriv_sourceDiscriminant_div_root
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h =
      deriv (fun w : ℂ =>
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
          sourceCanonicalRoot hp hp1 φ w) z := by
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  let G : ℂ → ℂ := fun w =>
    (fderiv ℂ (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h
  let Q : ℂ → ℂ := sourceCanonicalRoot hp hp1 φ
  have hF : AnalyticOnNhd ℂ F univ :=
    analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  have hG_eq : G = fun w : ℂ => (fderiv ℂ F (w,φ)) (0,h) := by
    funext w
    change (fderiv ℂ (fun b : CoeffPair p => F (w,b)) φ) h = _
    rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint F w φ
      ((hF (w,φ) (mem_univ _)).differentiableAt)]
    simp
  let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hjoint : AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p => (fderiv ℂ F t) (0,h)) univ :=
    ev.comp_analyticOnNhd hF.fderiv
  have hG : DifferentiableAt ℂ G z := by
    rw [hG_eq]
    exact ((hjoint (z,φ) (mem_univ _)).comp
      (f := fun w : ℂ => (w,φ))
      (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hQ : DifferentiableAt ℂ Q z :=
    (sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz).differentiableAt
  have hQne : Q z ≠ 0 :=
    sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz
  have hright := deriv_fun_div hG hQ hQne
  have hleft := fderiv_sourceCriticalRootRatioJoint_source hp hp1 φ hφ z hz h
  have hmixed := fderiv_source_discriminant_deriv_eq_deriv_spectral_fderiv_source
    hp hp1 z φ h
  have hroot := deriv_sourceCanonicalRoot_eq_discriminant_div_root_mul_deriv
    hp hp1 φ hφ z hz
  change (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h =
    deriv (fun w : ℂ => G w / Q w) z
  rw [hleft, hright]
  change _ = (deriv G z * Q z - G z * deriv Q z) / Q z ^ 2
  rw [← hmixed, hroot]
  dsimp [G, Q]
  ring

end NLS.ZakharovShabat
