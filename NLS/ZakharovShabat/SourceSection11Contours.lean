import NLS.ZakharovShabat.SourceActionContourFamily
import NLS.ZakharovShabat.SourceActionCircleAnalytic
import NLS.ZakharovShabat.SourceLemma10_11
import NLS.ComplexAnalysis.HolomorphicCircleIntegral
import NLS.ComplexAnalysis.BanachHolomorphicAnalytic

/-!
# Section 11 contours and analytic integrands on the retained domain

The simultaneous contour construction preserves all of Lemma 10.11 and
works inside every given original isolating family. Its fixed open collars
support the literal action integrand jointly in spectral and source
variables. Each fixed-circle action is analytic on the common local source
neighborhood. Independence of arbitrary circuits is a separate assertion.
-/

noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted integrand is jointly analytic on the full retained
moving-gap complement, with no additional restriction of W. -/
theorem SourceEquation2_15Data.actionIntegrand_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) :
    AnalyticOnNhd ℂ (sourceActionIntegrandJoint hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) :=
  fun t ht => analyticAt_fst.mul (h.joint.2 t ht)

/-- Every entire collar, uniformly over the same source neighborhood,
supports the literal integrand λΔ'(λ)/canonicalRoot(λ). -/
theorem SourceActionContourFamily.analytic_integrand_on_collar
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      t.1 * deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
        sourceCanonicalRoot hp hp1 t.2 t.1) (C.collar n ×ˢ V) := by
  have ha := h.actionIntegrand_joint.mono (show C.collar n ×ˢ V ⊆
      sourceCanonicalRootJointDomain hp hp1 W from
    fun t ht => ⟨hVW ht.2,C.collar_subset_rootDomain hD t.2 ht.2 n ht.1⟩)
  simpa only [sourceActionIntegrandJoint,sourceCriticalRootRatioJoint,mul_div_assoc] using! ha

/-- Every chosen fixed-circle action is analytic on the entire common
local source neighborhood, including its non-real sources. -/
theorem SourceActionContourFamily.analytic_actionCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n)) V := by
  apply analyticOnNhd_of_complexDifferentiableOn _ V hV
  intro ψ hψ
  have hsphere : ∀ z ∈ sphere (C.center n : ℂ) (C.radius n),
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W :=
    fun z hz => ⟨hVW hψ,C.collar_subset_rootDomain hD ψ hψ n (C.sphere_subset_collar n hz)⟩
  have hd := hasFDerivAt_circleIntegral_of_jointDifferentiable
    (sourceActionIntegrandJoint hp hp1) _ h.joint.1 h.actionIntegrand_joint.differentiableOn
    (C.center n : ℂ) (C.radius n) ((C.inner_pos n).trans (C.inner_lt n)).le ψ hsphere
  exact (hd.differentiableAt.const_mul (Real.pi : ℂ)⁻¹).differentiableWithinAt

/-- The opening contour assertions of Section 11, retaining the preceding
lemma and allowing every original isolating family at every source in W. -/
structure SourceSection11ContourData (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma10_11Data hp hp1 W
  contours : ∀ {V : Set (CoeffPair p)}, IsOpen V → V ⊆ W →
    ∀ {D : ℤ → Set ℂ} {c : ℝ}, SourceIsolatingNeighborhoods hp hp1 V D c →
    ∀ φ ∈ V, ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ C : SourceActionContourFamily hp hp1 U D, ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
          t.1 * deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
            sourceCanonicalRoot hp hp1 t.2 t.1) (C.collar n ×ˢ U) ∧
        AnalyticOnNhd ℂ (fun ψ => sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n)) U

/-- Extend the existing common-domain package without replacing W. -/
theorem SourceLemma10_11Data.actionContours
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_11Data hp hp1 W) : SourceSection11ContourData hp hp1 W := by
  refine ⟨h,?_⟩
  intro V hV hVW D c hD φ hφ
  have heq := h.previous.previous.previous
  obtain ⟨U,hU,hUc,hφU,hUV,⟨C⟩⟩ := heq.original_contourFamily hV hVW hD φ hφ
  exact ⟨U,hU,hUc,hφU,hUV,C,fun n =>
    ⟨C.analytic_integrand_on_collar heq (hUV.trans hVW) (hD.mono hUV) n,
      C.analytic_actionCircle heq hU (hUV.trans hVW) (hD.mono hUV) n⟩⟩

/-- Every source in W actually has one simultaneous contour neighborhood;
the preceding isolation theorem supplies its original disks. -/
theorem SourceSection11ContourData.neighborhoods
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ D c, SourceIsolatingNeighborhoods hp hp1 U D c ∧
        ∃ C : SourceActionContourFamily hp hp1 U D, ∀ n : ℤ,
          AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
            t.1 * deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
              sourceCanonicalRoot hp hp1 t.2 t.1) (C.collar n ×ˢ U) ∧
          AnalyticOnNhd ℂ (fun ψ => sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n)) U := by
  obtain ⟨V,hV,_,hφV,hVW,D,c,hD,_,_⟩ :=
    h.previous.previous.previous.previous.neighborhoods φ hφ
  obtain ⟨U,hU,hUc,hφU,hUV,C,ha⟩ := h.contours hV hVW hD.toSourceIsolatingNeighborhoods φ hφV
  exact ⟨U,hU,hUc,hφU,hUV.trans hVW,D,c,
    hD.toSourceIsolatingNeighborhoods.mono hUV,C,ha⟩

/-- The simultaneous Section 11 contours for every finite p>1, on the
unchanged open connected neighborhood of the entire real-type locus. -/
theorem sourceSection11Contours (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceSection11ContourData hp hp1 W := by
  obtain ⟨W,ho,hc,hr,h⟩ := sourceLemma10_11 hp hp1
  exact ⟨W,ho,hc,hr,h.actionContours⟩

end NLS.ZakharovShabat
