import NLS.ZakharovShabat.SourceLemma10_2
import NLS.ZakharovShabat.SourceStandardRootNorm
import NLS.ZakharovShabat.SourceStandardRootPiecewiseContour
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceJoint

/-!
# Lemma 10.3 on the same almost-real domain as Lemma 10.2

The actual normalized root is analytic off its moving gap and jointly
analytic outside each fixed isolating disk. The same distance constant
bounds every distinct-index root. Actual piecewise C¹ contour integrals
have the negative Kronecker-delta normalization.
-/

noncomputable section
open Set Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The isolating point-pair distance constant also bounds every distinct-index root. -/
theorem SourceIsolatingNeighborhoods.standardRoot_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (m n : ℤ) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ D m) :
    c⁻¹*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
      ‖sourceStandardRoot hp hp1 ψ n z‖ ≤ c*|((m-n : ℤ) : ℝ)| := by
  have hc : 0 < c := zero_lt_one.trans_le h.one_le
  have hznot : z ∉ sourcePeriodicSegment hp hp1 ψ n :=
    fun hg => Set.disjoint_left.mp (h.disjoint m n hmn) hz (h.gap ψ hψ n hg)
  have hL := h.pointwise_distance m n hmn z hz _ (h.cluster ψ hψ n (Or.inl rfl))
  have hR := h.pointwise_distance m n hmn z hz _ (h.cluster ψ hψ n (Or.inr (Or.inl rfl)))
  rw [dist_comm,dist_eq_norm] at hL hR
  exact sourceStandardRoot_norm_bounds_of_endpoint_bounds hp hp1 ψ n z hznot _ _
    (mul_nonneg (inv_nonneg.mpr hc.le) (abs_nonneg _))
    (mul_nonneg hc.le (abs_nonneg _)) hL.1 hR.1 hL.2 hR.2

/-- Joint analyticity on the full moving-gap complement uses the Lemma 10.2 domain unchanged. -/
theorem SourceLemma10_2Data.standardRoot_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_2Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p => sourceStandardRoot hp hp1 q.2 n q.1)
      {q | q.2 ∈ W ∧ q.1 ∉ sourcePeriodicSegment hp hp1 q.2 n} := by
  intro q hq
  exact sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 q.2 n q.1
    (h.midpoint n q.2 hq.1) (h.squared_gap n q.2 hq.1) hq.2

/-- In particular the root is jointly analytic outside each fixed local isolating disk. -/
theorem SourceLemma10_2Data.standardRoot_local
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_2Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p => sourceStandardRoot hp hp1 q.2 n q.1)
      ((D n)ᶜ ×ˢ V) := by
  intro q hq
  exact h.standardRoot_joint n q ⟨hVW hq.2,fun hseg => hq.1 (hD.gap q.2 hq.2 n hseg)⟩


/-- All local assertions use the same source neighborhood, disks and constant. -/
structure SourceStandardRootNeighborhoods (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) (c : ℝ) : Prop extends
    SourceIsolatingNeighborhoods hp hp1 V D c where
  joint : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun q : ℂ × CoeffPair p => sourceStandardRoot hp hp1 q.2 n q.1) ((D n)ᶜ ×ˢ V)
  bounds : ∀ ψ ∈ V, ∀ m n : ℤ, m ≠ n → ∀ z ∈ D m,
    c⁻¹*|((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
      ‖sourceStandardRoot hp hp1 ψ n z‖ ≤ c*|((m-n : ℤ) : ℝ)|
  contours : ∀ ψ ∈ V, ∀ m n : ℤ, ∀ Γ : PiecewiseC1Loop,
    Γ.Inside (D m) → Γ.Inside (sourcePeriodicSegment hp hp1 ψ m)ᶜ →
    Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) = 1 →
    Γ.normalizedIntegral (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      if m = n then -1 else 0

/-- The common domain retains Lemma 10.2 and supplies every assertion of Lemma 10.3. -/
structure SourceLemma10_3Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  symmetric : SourceLemma10_2Data hp hp1 W
  spectral : ∀ ψ : CoeffPair p, ∀ n : ℤ,
    AnalyticOnNhd ℂ (sourceStandardRoot hp hp1 ψ n) (sourcePeriodicSegment hp hp1 ψ n)ᶜ
  joint : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun q : ℂ × CoeffPair p => sourceStandardRoot hp hp1 q.2 n q.1)
    {q | q.2 ∈ W ∧ q.1 ∉ sourcePeriodicSegment hp hp1 q.2 n}
  neighborhoods : ∀ ψ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ ψ ∈ V ∧ V ⊆ W ∧
    ∃ D c, SourceStandardRootNeighborhoods hp hp1 V D c

/-- Lemma 10.2's domain already supports all of Lemma 10.3, without further shrinking. -/
theorem SourceLemma10_2Data.standardRoots {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W : Set (CoeffPair p)} (h : SourceLemma10_2Data hp hp1 W) : SourceLemma10_3Data hp hp1 W := by
  refine ⟨h,sourceStandardRoot_analyticOnNhd hp hp1,h.standardRoot_joint,?_⟩
  intro ψ hψ
  obtain ⟨V,hVo,hVc,hψV,hVW,D,c,hD⟩ := h.isolation ψ hψ
  exact ⟨V,hVo,hVc,hψV,hVW,D,c,hD,h.standardRoot_local hVW hD,
    hD.standardRoot_bounds,hD.standardRoot_piecewiseIntegral_indexed⟩

/-- Lemma 10.3 for every finite p>1, with all previous common-domain assertions retained. -/
theorem sourceLemma10_3 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma10_3Data hp hp1 W := by
  obtain ⟨W,ho,hc,hreal,h⟩ := sourceLemma10_2 hp hp1
  exact ⟨W,ho,hc,hreal,h.standardRoots⟩

/-- A collapsed gap gives an entire linear root, including the otherwise excluded midpoint. -/
theorem sourceStandardRoot_analyticOnNhd_of_zeroGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    AnalyticOnNhd ℂ (sourceStandardRoot hp hp1 ψ n) univ := by
  have heq : sourceStandardRoot hp hp1 ψ n = fun z =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z :=
    funext (fun z => sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap)
  rw [heq]
  exact analyticOnNhd_const.sub analyticOnNhd_id

end NLS.ZakharovShabat
