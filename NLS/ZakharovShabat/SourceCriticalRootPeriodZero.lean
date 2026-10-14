import NLS.ZakharovShabat.SourceCriticalRootPeriod
import NLS.ZakharovShabat.SourceCriticalRootRatioAnyCircleZero
import NLS.ZakharovShabat.SourceLemma10_11i
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Vanishing periods on the unchanged connected source domain

A real base supplies an open zero germ. The circle-independent period is
analytic throughout W, so the identity principle propagates that germ
across W. Every original isolating circle consequently has zero period,
including at complex sources outside the initial real-base neighborhood.
The arbitrary endpoint-path assertion of Lemma 10.11(ii) is separate.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single real base in the connected common domain forces every indexed
period to vanish throughout that same domain. -/
theorem SourceEquation2_15Data.period_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hW : IsOpen W) (hconn : IsPreconnected W)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W)
    (n : ℤ) : EqOn (sourceCriticalRootPeriod hp hp1 n) 0 W := by
  obtain ⟨V,hV,_,hφV,_,D,c,hD,_,_⟩ := h.neighborhoods φ hφW
  obtain ⟨a,r,hr,he⟩ := hD.toSourceIsolatingNeighborhoods.discs n
  have hgeom : ∀ ψ ∈ V, sourcePeriodicSegment hp hp1 ψ n ⊆ ball (a : ℂ) r ∧
      closedBall (a : ℂ) r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro ψ hψ
    let C := hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψ n a r hr he
    exact ⟨C.gap,C.closedBall_subset_omittedDomain⟩
  obtain ⟨U,hU,hφU,hUV,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_givenCircle
      hp hp1 φ hφ n V hV hφV (a : ℂ) r hr hgeom
  have hgerm : sourceCriticalRootPeriod hp hp1 n =ᶠ[𝓝 φ] 0 := by
    filter_upwards [hU.mem_nhds hφU] with ψ hψ
    change sourceCriticalRootPeriod hp hp1 n ψ = 0
    rw [hD.toSourceIsolatingNeighborhoods.period_eq_originalCircle n a r hr he ψ (hUV hψ)]
    exact hzero ψ hψ
  exact (h.analytic_period hW n).eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hφW hgerm

/-- The vanishing statement applies to any original family, at every
complex source in W, with its boundary radius unchanged. -/
theorem SourceEquation2_15Data.originalCircle_integral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hW : IsOpen W) (hconn : IsPreconnected W)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n : ℤ) (a r : ℝ) (hr : 0 < r) (he : D n = ball (a : ℂ) r) :
    (∮ z in C((a : ℂ),r), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  rw [← hD.period_eq_originalCircle n a r hr he ψ hψV]
  exact h.period_eq_zero hW hconn φ hφ hφW n hψW

/-- The circle-period portion of Lemma 10.11(ii), retaining full part (i). -/
structure SourceLemma10_11CircleData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_11iData hp hp1 W
  analytic_period : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceCriticalRootPeriod hp hp1 n) W
  zero : ∀ ψ ∈ W, ∀ n : ℤ, ∀ D : SourceCriticalRootPeriodCircle hp hp1 ψ n,
    (∮ z in C((D.center : ℂ),D.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0

/-- Add vanishing periods without shrinking the existing connected W. -/
theorem SourceLemma10_11iData.zeroPeriods
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11iData hp hp1 W) (hW : IsOpen W)
    (hconn : IsConnected W) (hreal : realTypeSourceLocus p ⊆ W) :
    SourceLemma10_11CircleData hp hp1 W := by
  refine ⟨h,h.previous.analytic_period hW,?_⟩
  intro ψ hψ n D
  rw [← sourceCriticalRootPeriod_eq_circle D]
  exact h.previous.period_eq_zero hW hconn.isPreconnected 0 (by simp)
    (hreal (by simp [realTypeSourceLocus])) n hψ

/-- Every finite p>1 admits the original common domain with all original
circle periods zero, as well as the analytic continuation in part (i). -/
theorem sourceLemma10_11CirclePeriods (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_11CircleData hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_11i hp hp1
  exact ⟨W,ho,hc,hr,h.zeroPeriods ho hc hr⟩

end NLS.ZakharovShabat
