import NLS.ZakharovShabat.SourceAngularActionKernelPeriod
import NLS.ZakharovShabat.SourceRealActionRealCenteredChart
import NLS.ZakharovShabat.SourcePsiRealContourComparison

/-! # The actual canonical theta/action brackets

The actual full terminal kernel sum has two proved limits: the
theta/action bracket and the normalized psi period on an action circle.
Real-centered action charts exist at every real source, and actual
contour comparison transfers the normalized psi period to that circle.
Their common limit is the Kronecker delta.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual normalized psi period on every real-centered action
chart has the original Kronecker normalization. -/
theorem psi_period_on_realCentered_action_chart
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n k : ℤ) (ch : SourceRealActionBallChart hp hp1 k) (hc : ch.spectralCenter.im = 0)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ ball ch.center ch.radius) :
    (2*Real.pi : ℂ)⁻¹*(∮ w in C(ch.spectralCenter,ch.spectralRadius),
      sourcePsiContourIntegrandJoint hp hp1 n (w,((s n φ.val : Coeff p),φ.val))) =
      if n = k then 1 else 0 := by
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨r,hr,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  have hφ₀ : φ.val ∈ W₀ := hball (mem_ball_self hr)
  obtain ⟨c,R,hfamily,hperiod⟩ := D.psi.contour_orthogonality φ.val hφ₀
  have hgeom := ch.geometry φ.val hφ
  have he := sourcePsiContour_eq_of_realCentered_enclosingCircles hp hp1 n k
    (s n φ.val : Coeff p) φ.val φ.property ch.spectralCenter (c k) ch.spectralRadius (R k)
    hc (hfamily.1 k) ch.spectralRadius_pos (hfamily.2 k).1
    hgeom.1 (hfamily.2 k).2.1 hgeom.2 (hfamily.2 k).2.2.1
  change sourcePsiContour hp hp1 n (s n φ.val : Coeff p) φ.val ch.spectralCenter ch.spectralRadius = _
  simpa only [eq_comm] using he.trans (hperiod n k)

/-- The actual theta/action bracket equals the Kronecker delta on
every real-centered action chart, including branch terminals. -/
theorem thetaAction_eq_kronecker_on_realCentered_chart
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ)
    (ch : SourceRealActionBallChart hp hp1 k) (hc : ch.spectralCenter.im = 0)
    (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hφ : φ.val ∈ ball ch.center ch.radius) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val =
      if n = k then 1 else 0 := by
  have ht := D.tendsto_thetaActionKernelSum h2p n k ch φ hgap hφ
  have hi := tendsto_sourcePsiDirichlet_actionKernelSums hp hp1 n k (s n φ.val : Coeff p) ch φ hφ
  change Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
    sourceAngularActionKernelTerm hp hp1 n k ch s φ.val m) atTop
    (𝓝 ((2*Real.pi : ℂ)⁻¹*(∮ w in C(ch.spectralCenter,ch.spectralRadius),
      sourcePsiContourIntegrandJoint hp hp1 n (w,((s n φ.val : Coeff p),φ.val))))) at hi
  rw [D.psi_period_on_realCentered_action_chart n k ch hc φ hφ] at hi
  exact tendsto_nhds_unique ht hi

/-- The actual canonical angle/action identity at every real source
with an open selected angle gap, with no supplied action or angle chart. -/
theorem thetaAction_eq_kronecker
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) φ.val =
      if n = k then 1 else 0 := by
  obtain ⟨ch,hcenter,hc⟩ := exists_sourceRealActionBallChart_realCentered hp hp1 k φ
  have hφ : φ.val ∈ ball ch.center ch.radius := by rw [hcenter]; exact mem_ball_self ch.radius_pos
  exact D.thetaAction_eq_kronecker_on_realCentered_chart h2p n k ch hc φ hgap hφ

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
