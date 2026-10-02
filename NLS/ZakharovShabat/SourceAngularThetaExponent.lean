import NLS.ZakharovShabat.SourceAngularEtaPhaseExponent
import NLS.ZakharovShabat.SourceAngularBetaExponentDifferential
import NLS.ZakharovShabat.SourceAngularThetaDifferential

/-! # Exponent compatibility of the full angle phase and differential

The actual eta phase and beta correction identify the full theta phase
at every real open gap. Real-form uniqueness extends this identity to a
complex neighborhood. Its derivative identifies the actual logarithmic
angle cotangent under coefficient-preserving source inclusion.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
  {W₀ B W : Set (CoeffPair p)} {V₀ C V : Set (CoeffPair q)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

theorem thetaPhase_real_exponent_agreement
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularThetaAnalyticPhase hp hp1 n s φ.val =
      sourceAngularThetaAnalyticPhase hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) := by
  unfold sourceAngularThetaAnalyticPhase
  rw [D.etaPhase_real_exponent_agreement E hpq n φ hgap,
    D.psi.toSourcePsiIsolatingComplexExtension.betaCorrection_real_exponent_agreement
      E.psi.toSourcePsiIsolatingComplexExtension hpq n φ]

/-- Analyticity upgrades real phase compatibility to equality on a
complex neighborhood of every real source with the selected gap open. -/
theorem eventually_thetaPhase_exponent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularThetaAnalyticPhase hp hp1 n s =ᶠ[𝓝 φ.val]
      (sourceAngularThetaAnalyticPhase hq hq1 n t ∘ CoeffPair.exponentInclusion hpq) := by
  have hgap' : canonicalPeriodicGap hq hq1
      (periodOnePotential (CoeffPair.exponentInclusion hpq φ.val)) (periodOnePotential_mem _) n ≠ 0 := by
    rw [← canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq φ.val n]
    exact hgap
  let F := sourceAngularThetaAnalyticPhase hp hp1 n s
  let G := sourceAngularThetaAnalyticPhase hq hq1 n t ∘ CoeffPair.exponentInclusion hpq
  have hφW := D.real_subset φ.property
  have hF : AnalyticAt ℂ F φ.val := D.theta_phase_analytic n φ.val ⟨hφW,hgap⟩
  have hG : AnalyticAt ℂ G φ.val :=
    (E.theta_phase_analytic n (CoeffPair.exponentInclusion hpq φ.val)
      ⟨E.real_subset (realTypeSourceExponentInclusion hpq φ).property,hgap'⟩).comp
        (f := CoeffPair.exponentInclusion hpq) (x := φ.val)
        ((CoeffPair.exponentInclusion hpq).analyticAt _)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((hF.eventually_analyticAt.and hG.eventually_analyticAt).and
      ((D.open_gap n).mem_nhds ⟨hφW,hgap⟩))
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r F G
    (fun ψ hψ => (hball hψ).1.1.differentiableAt.differentiableWithinAt)
    (fun ψ hψ => (hball hψ).1.2.differentiableAt.differentiableWithinAt)
    (fun χ hχ => D.thetaPhase_real_exponent_agreement E hpq n χ (hball hχ.1).2.2)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ψ hψ
  exact heq ⟨hψ,hψ⟩

theorem fderiv_thetaPhase_exponent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    fderiv ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s) φ.val =
      (fderiv ℂ (sourceAngularThetaAnalyticPhase hq hq1 n t)
        (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  have hgap' : canonicalPeriodicGap hq hq1
      (periodOnePotential (CoeffPair.exponentInclusion hpq φ.val)) (periodOnePotential_mem _) n ≠ 0 := by
    rw [← canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq φ.val n]
    exact hgap
  rw [(D.eventually_thetaPhase_exponent E hpq n φ hgap).fderiv_eq]
  rw [fderiv_comp φ.val
    (E.theta_phase_analytic n (CoeffPair.exponentInclusion hpq φ.val)
      ⟨E.real_subset (realTypeSourceExponentInclusion hpq φ).property,hgap'⟩).differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt, ContinuousLinearMap.fderiv]

/-- The actual angle cotangent is exponent compatible over the entire
finite range above one. It includes every contribution from moving
roots, angle branches, and the beta correction. -/
theorem thetaDifferential_exponent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularThetaDifferential hp hp1 n s φ.val =
      (sourceAngularThetaDifferential hq hq1 n t
        (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  unfold sourceAngularThetaDifferential
  rw [D.thetaPhase_real_exponent_agreement E hpq n φ hgap,
    D.fderiv_thetaPhase_exponent E hpq n φ hgap, ContinuousLinearMap.smul_comp]

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
