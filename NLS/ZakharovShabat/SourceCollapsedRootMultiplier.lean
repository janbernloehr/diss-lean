import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumPath
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy
import NLS.ComplexAnalysis.NonrealContinuousIdentity
import NLS.ComplexAnalysis.CollapsedLinearFactorDerivative

/-! The ACTUAL omitted root multiplier at a collapsed gap. Its product
with the filled critical quotient is determined by trace curvature,
including sign. Nothing is divided by the vanished selected root. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceGapRootMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p) (z : ℂ) : ℂ :=
  2*I*sourceStandardRootOmittedProduct hp hp1 n φ z

theorem analyticOnNhd_sourceGapRootMultiplier_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticOnNhd ℂ (sourceGapRootMultiplier hp hp1 n φ)
      (sourceStandardRootOmittedDomain hp hp1 φ n) := by
  obtain ⟨V,_,_,hVreal,hprod⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  intro z hz
  have hO := ((hprod n).2.1 (z,φ) ⟨hVreal hreal,hz⟩).comp
    (f := fun w : ℂ => (w,φ)) (analyticAt_id.prod analyticAt_const)
  exact analyticAt_const.mul hO

theorem sourceGapRootMultiplier_collapsed_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n=0)
    (z : ℂ) (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 φ n) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
      sourceCriticalRootRatioExtension hp hp1 n φ z*
        (sourceStandardRootMidpoint hp hp1 φ n-z)*sourceGapRootMultiplier hp hp1 n φ z := by
  let Ω := sourceStandardRootOmittedDomain hp hp1 φ n
  let E := sourceCriticalRootRatioExtension hp hp1 n φ
  let K := sourceGapRootMultiplier hp hp1 n φ
  let τ := sourceStandardRootMidpoint hp hp1 φ n
  let D := canonicalDiscriminant hp (periodOnePotential φ)
  obtain ⟨W,_,hWreal,hEdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  have hE := (hEdata φ (hWreal hreal) n hgap).1
  have hK := analyticOnNhd_sourceGapRootMultiplier_of_realType hp hp1 n φ hreal
  have hD : AnalyticOnNhd ℂ D univ := by
    intro w _
    exact (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (w,φ) (mem_univ _)).comp
      (f := fun v : ℂ => (v,φ)) (analyticAt_id.prod analyticAt_const)
  have hF : ContinuousOn (fun w => E w*(τ-w)*K w) Ω :=
    (hE.continuousOn.mul (continuous_const.sub continuous_id).continuousOn).mul hK.continuousOn
  have hG : ContinuousOn (deriv D) Ω := (hD.deriv.continuous).continuousOn
  have heoff (w : ℂ) (_hw : w ∈ Ω) (hwi : w.im ≠ 0) : E w*(τ-w)*K w=deriv D w := by
    have hw := sourceCanonicalRootDomain_of_im_ne_zero hp hp1 φ hreal w hwi
    have hroot : (τ-w)*K w=sourceCanonicalRoot hp hp1 φ w := by
      rw [sourceCanonicalRoot_eq_omitted hp hp1 n φ w,
        sourceStandardRoot_of_zeroGap hp hp1 φ n w (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)]
      change (τ-w)*(2*I*sourceStandardRootOmittedProduct hp hp1 n φ w) =
        2*I*(τ-w)*sourceStandardRootOmittedProduct hp hp1 n φ w
      ring
    rw [mul_assoc,hroot]
    change sourceCriticalRootRatioExtension hp hp1 n φ w*sourceCanonicalRoot hp hp1 φ w =
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) w
    rw [(hEdata φ (hWreal hreal) n hgap).2 w hw]
    exact div_mul_cancel₀ _ (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ w hw)
  exact (NLS.ComplexAnalysis.ContinuousOn.eqOn_of_nonreal
    (isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 φ hreal n) hF hG heoff hz).symm

theorem sourceGapRootMultiplier_collapsed_curvature
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hgap : sourcePeriodicGapDisplacement hp hp1 φ n=0) :
    deriv (deriv (canonicalDiscriminant hp (periodOnePotential φ)))
        (sourceStandardRootMidpoint hp hp1 φ n) =
      -sourceCriticalRootRatioExtension hp hp1 n φ (sourceStandardRootMidpoint hp hp1 φ n)*
        sourceGapRootMultiplier hp hp1 n φ (sourceStandardRootMidpoint hp hp1 φ n) := by
  let τ := sourceStandardRootMidpoint hp hp1 φ n
  let Ω := sourceStandardRootOmittedDomain hp hp1 φ n
  have hΩ := isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 φ hreal n
  have hτ : τ ∈ Ω := by
    obtain ⟨V,_,_,hVreal,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
    intro m hmn hm
    exact Set.disjoint_left.mp (hdisjoint φ (hVreal hreal) n m (Ne.symm hmn))
      (sourcePeriodicMidpoint_mem_segment hp hp1 φ n) hm
  obtain ⟨W,_,hWreal,hEdata⟩ := exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  have hE := ((hEdata φ (hWreal hreal) n hgap).1 τ hτ).differentiableAt
  have hK := (analyticOnNhd_sourceGapRootMultiplier_of_realType hp hp1 n φ hreal τ hτ).differentiableAt
  apply deriv_eq_of_collapsed_linear_factor _ _ _ τ hE hK
  filter_upwards [hΩ.mem_nhds hτ] with z hz
  exact sourceGapRootMultiplier_collapsed_factor hp hp1 n φ hreal hgap z hz

end NLS.ZakharovShabat
