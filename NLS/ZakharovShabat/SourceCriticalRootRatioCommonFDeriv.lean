import NLS.ZakharovShabat.SourceCanonicalRootCommonFDeriv
import NLS.ZakharovShabat.SourceCriticalRootRatioSourceFDeriv

/-!
# Mixed derivatives of the critical-root quotient throughout W

On the retained common source domain, differentiating Δ'/Q in a source
direction equals the spectral derivative of the discriminant variation
Δ_h/Q. This includes every complex source, with no restriction on which
gaps are collapsed.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source Fréchet derivative of the critical-root quotient at a
complex source in the retained W, away from all moving periodic cuts. -/
theorem SourceEquation2_15Data.criticalRatio_source_fderiv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W)
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
    exact ((H.previous.previous.previous.joint.2 (z,φ) ⟨hφ,hz⟩).comp
      (f := fun ψ : CoeffPair p => (z,ψ))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hquot := NLS.ComplexAnalysis.fderiv_div_apply N Q φ hN hQ
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz) h
  rw [H.root_source_fderiv φ hφ z hz h] at hquot
  exact hquot

/-- The source derivative of `Δ' / Q` is a spectral derivative:
`∂₍φ₎(Δ' / Q) = ∂₍z₎((∂₍φ₎Δ) / Q)`. This is the pointwise
identity needed for the action contour integration by parts. -/
theorem SourceEquation2_15Data.criticalRatio_source_fderiv_eq_spectral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_15Data hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W)
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
  have hleft := H.criticalRatio_source_fderiv φ hφ z hz h
  have hmixed := fderiv_source_discriminant_deriv_eq_deriv_spectral_fderiv_source
    hp hp1 z φ h
  have hroot := H.root_spectral_deriv φ hφ z hz
  change (fderiv ℂ (fun ψ : CoeffPair p =>
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h =
    deriv (fun w : ℂ => G w / Q w) z
  rw [hleft, hright]
  change _ = (deriv G z * Q z - G z * deriv Q z) / Q z ^ 2
  rw [← hmixed, hroot]
  dsimp [G, Q]
  ring

end NLS.ZakharovShabat
