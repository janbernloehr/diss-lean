import NLS.ComplexAnalysis.QuadraticCauchyUniqueness
import NLS.ZakharovShabat.SourceAngularCauchyEquation
import NLS.ZakharovShabat.SourceAngularIntegrandIsospectral

/-! # The actual interior angular Cauchy candidate is isospectral

Differentiate its actual quadratic equation. Its symmetric coefficients
and actual regular gap numerator are stationary. Commuting the spectral
and source derivatives gives a homogeneous equation for its variation.
Analytic uniqueness on the enclosing disc forces that variation to zero,
including at periodic endpoints and collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual off-diagonal Cauchy candidate is stationary on the
whole interior disc in every isospectral direction. No exclusion of
periodic endpoints or collapsed gaps is needed. -/
theorem fderiv_quotientCauchyCandidate_isospectral_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n : ℤ) (hmn : m ≠ n) (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h)
    (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceAngularQuotientCauchyCandidate
      hp hp1 n m s (c m) r R z₀ ρ (z,ψ)) φ.val) h = 0 := by
  let H := sourceAngularQuotientCauchyCandidate hp hp1 n m s (c m) r R z₀ ρ
  let Ω := ball (c m) ρ
  let X := Ω ×ˢ V
  have hX : IsOpen X := isOpen_ball.prod D.source_open
  have hH : AnalyticOnNhd ℂ H X := D.analyticOnNhd_quotientCauchyCandidate n ρ hrρ hρR
  let J : ℂ → ℂ := fun w => (fderiv ℂ (fun ψ : CoeffPair p => H (w,ψ)) φ.val) h
  let ev₀ : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  let ev₁ : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hJjoint : AnalyticOnNhd ℂ (fun t => (fderiv ℂ H t) (0,h)) X := ev₀.comp_analyticOnNhd hH.fderiv
  have hCjoint : AnalyticOnNhd ℂ (fun t => (fderiv ℂ H t) (1,0)) X := ev₁.comp_analyticOnNhd hH.fderiv
  have hJ : AnalyticOnNhd ℂ J Ω := by
    intro w hw
    have ha := (hJjoint (w,φ.val) ⟨hw,hφ⟩).comp
      (f := fun v : ℂ => (v,φ.val)) (analyticAt_id.prod analyticAt_const)
    have heq : J =ᶠ[𝓝 w] (fun v => (fderiv ℂ H (v,φ.val)) (0,h)) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      dsimp only [J]
      rw [fderiv_source_section_eq_joint H v φ.val (hH (v,φ.val) ⟨hv,hφ⟩).differentiableAt]
      simp
    exact ha.congr heq.symm
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2
  obtain ⟨A,_,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ.val := (hMG φ.val (hAreal φ.property) m).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ.val := (hMG φ.val (hAreal φ.property) m).2.differentiableAt
  have hMGzero : (fderiv ℂ M φ.val) h = 0 ∧ (fderiv ℂ G φ.val) h = 0 :=
    fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m
  have hzero (w : ℂ) (hw : w ∈ Ω) :
      sourceAngularSelectedPolynomial hp hp1 φ.val m w*deriv J w+(w-M φ.val)*J w = 0 := by
    let B : CoeffPair p → ℂ := fun ψ => w-M ψ
    let C : CoeffPair p → ℂ := fun ψ => deriv (fun v => H (v,ψ)) w
    have hHsource : DifferentiableAt ℂ (fun ψ : CoeffPair p => H (w,ψ)) φ.val :=
      ((hH (w,φ.val) ⟨hw,hφ⟩).comp
        (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hC : DifferentiableAt ℂ C φ.val := by
      have ha := (hCjoint (w,φ.val) ⟨hw,hφ⟩).comp
        (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)
      have heq : C =ᶠ[𝓝 φ.val] (fun ψ => (fderiv ℂ H (w,ψ)) (1,0)) := by
        filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
        exact deriv_spectral_section_eq_fderiv H w ψ (hH (w,ψ) ⟨hw,hψ⟩).differentiableAt
      exact (ha.congr heq.symm).differentiableAt
    have hB := (hasFDerivAt_const w φ.val).fun_sub hM.hasFDerivAt
    have hpoly := (hB.pow 2).fun_sub (hG.hasFDerivAt.mul_const (4 : ℂ)⁻¹)
    have hpolyzero : (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceAngularSelectedPolynomial hp hp1 ψ m w) φ.val) h = 0 := by
      have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hpoly.fderiv
      change (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceAngularSelectedPolynomial hp hp1 ψ m w) φ.val) h = _ at he
      simp only [sub_apply,smul_apply,smul_eq_mul,zero_apply,hMGzero.1,hMGzero.2,
        sub_self,mul_zero] at he
      exact he
    have hBzero : (fderiv ℂ B φ.val) h = 0 := by
      rw [hB.fderiv]
      simp [hMGzero.1]
    have hL := (hpoly.fun_mul hC.hasFDerivAt).fun_add (hB.fun_mul hHsource.hasFDerivAt)
    have hnear : (fun ψ : CoeffPair p => sourceAngularSelectedPolynomial hp hp1 ψ m w*C ψ+
        B ψ*H (w,ψ)) =ᶠ[𝓝 φ.val] (fun ψ => sourceAngularGapNumerator hp hp1 n m s ψ w) := by
      filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
      exact D.quotientCauchyCandidate_equation ψ hψ n hmn ρ hrρ hρR w hw
    have he := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hnear.fderiv_eq
    have hLderiv := hL.fderiv
    change fderiv ℂ (fun ψ : CoeffPair p => sourceAngularSelectedPolynomial hp hp1 ψ m w*C ψ+
      B ψ*H (w,ψ)) φ.val = _ at hLderiv
    rw [hLderiv] at he
    have hother : w ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m :=
      ((D.disc_family φ.val hφ).contour_family.2 m).2.2.1
        (ball_subset_closedBall (ball_subset_ball (hρR.trans D.outer_lt_assigned).le hw))
    rw [hs.fderiv_angularGapNumerator_isospectral_eq_zero n m φ hφ₀ h hiso w hother] at he
    have hpolyEval := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hpoly.fderiv
    change (fderiv ℂ (fun ψ : CoeffPair p => sourceAngularSelectedPolynomial hp hp1 ψ m w) φ.val) h = _ at hpolyEval
    have hBEval := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hB.fderiv
    have hcomm := fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source
      H X hX hH w φ.val ⟨hw,hφ⟩ h
    simp only [add_apply,smul_apply,smul_eq_mul] at he
    rw [← hpolyEval,hpolyzero,← hBEval,hBzero,mul_zero,mul_zero,add_zero,add_zero,hcomm] at he
    exact he
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m
  have ha : a ∈ Ω := ball_subset_ball hrρ.le (D.gap_enclosed φ.val hφ (left_mem_segment ℝ a b))
  exact quadratic_equation_homogeneous_eq_zero a b J Ω isOpen_ball (convex_ball (c m) ρ).isPreconnected ha hJ hzero z hz

/-- Every actual action commutes with the fixed-parameter interior
Cauchy candidate, throughout its enclosing disc. -/
theorem sourceBracket_quotientCauchyCandidate_action_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (hmn : m ≠ n)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAngularQuotientCauchyCandidate
      hp hp1 n m s (c m) r R z₀ ρ (z,ψ)) (sourceComplexAction hp hp1 k) φ.val = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact D.fderiv_quotientCauchyCandidate_isospectral_eq_zero hs n hmn ρ hrρ hρR φ hφ hφ₀ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k) z hz

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
