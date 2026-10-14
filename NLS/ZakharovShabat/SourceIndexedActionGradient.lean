import NLS.ZakharovShabat.SourceEquation2_16
import NLS.ZakharovShabat.SourceActionCommonGradient
import NLS.ComplexAnalysis.PiecewiseContourOuterPeriod

/-!
# The indexed action gradient and complex collapsed gaps

The derivative of the indexed action is computed on every original circle
and every admissible counterclockwise piecewise C¹ circuit. The continued
quotient from Lemma 10.11 also proves zero action at every collapsed complex
gap. All results use the unchanged source domain W.
-/

noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed original circle computes the derivative of the indexed function. -/
theorem SourceEquation2_16Data.original_circle_gradient
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_16Data hp hp1 W) (hV : IsOpen V)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (n : ℤ) (a R : ℝ) (hR : 0 < R) (he : D n = ball (a : ℂ) R) (v : CoeffPair p) :
    (fderiv ℂ (sourceIndexedAction hp hp1 n) ψ) v =
      -(Real.pi : ℂ)⁻¹*(∮ z in C((a : ℂ),R),
        (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) v /
          sourceCanonicalRoot hp hp1 ψ z) := by
  have hloc : sourceIndexedAction hp hp1 n =ᶠ[𝓝 ψ]
      (fun χ => sourceActionCircle hp hp1 χ (a : ℂ) R) := by
    filter_upwards [hV.mem_nhds hψV] with χ hχ
    exact hD.action_eq_originalCircle n a R hR he χ hχ
  rw [hloc.fderiv_eq]
  have Hq : SourceEquation2_15Data hp hp1 W := H.previous.previous.previous.previous.previous
  exact Hq.fderiv_actionCircle_eq_gradient_integral ψ hψW (a : ℂ) R hR
    (hD.periodCircle ψ hψV n a R hR he).sphere_subset_rootDomain v

/-- Equation (2.17) for any admissible counterclockwise piecewise C¹ circuit
in any original isolating disk, at arbitrary complex sources in W. -/
theorem SourceEquation2_16Data.circuit_gradient
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_16Data hp hp1 W) (hV : IsOpen V)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1)
    (v : CoeffPair p) :
    (fderiv ℂ (sourceIndexedAction hp hp1 n) ψ) v =
      -(Real.pi : ℂ)⁻¹*Γ.integral (fun z =>
        (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) v /
          sourceCanonicalRoot hp hp1 ψ z) := by
  obtain ⟨a,R,hR,he⟩ := hD.discs n
  let C := hD.periodCircle ψ hψV n a R hR he
  obtain ⟨r,s,hr,hrs,hsR,hsegr⟩ :=
    exists_nested_radii_of_segment_subset_ball _ _ (a : ℂ) R C.gap
  have hclosed : IsClosed (sourcePeriodicSegment hp hp1 ψ n) := by
    apply IsCompact.isClosed
    change IsCompact (segment ℝ _ _)
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hmid := sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  let f : ℂ → ℂ := fun z =>
    (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) v /
      sourceCanonicalRoot hp hp1 ψ z
  have hana : AnalyticOnNhd ℂ f (closedBall (a : ℂ) R \ sourcePeriodicSegment hp hp1 ψ n) := by
    apply (analyticOnNhd_sourceDiscriminantVariation_div_root hp hp1 ψ v).mono
    intro z hz m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact C.closedBall_subset_omittedDomain hz.1 m hm
  have hΓ' : Γ.Inside (ball (a : ℂ) R \ sourcePeriodicSegment hp hp1 ψ n) := by rwa [← he]
  have hperiod := Γ.integral_eq_outerCircleIntegral_mul_winding_of_starConvex_cut
    f (a : ℂ) _ r R hr (hrs.trans hsR) _ hclosed hmid ((convex_segment _ _).starConvex hmid) hsegr hana hΓ'
  rw [hw,mul_one] at hperiod
  rw [H.original_circle_gradient hV hD ψ hψW hψV n a R hR he v]
  change -(Real.pi : ℂ)⁻¹*(∮ z in C((a : ℂ),R), f z) = -(Real.pi : ℂ)⁻¹*Γ.integral f
  rw [hperiod]

/-- A collapsed gap gives zero action even at a non-real source in W. -/
theorem SourceEquation2_16Data.indexedAction_zero_of_gap_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_16Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    sourceIndexedAction hp hp1 n ψ = 0 := by
  obtain ⟨U,_,_,hψU,hUW,D,c,hD,C,_⟩ := H.previous.neighborhoods ψ hψ
  have Hc : SourceLemma10_11iData hp hp1 W := H.previous.previous.previous.previous
  have hana := (Hc.continued_analytic_originalDisk hUW hD ψ hψU n hg).1
  let f := sourceCriticalRootRatioContinued hp hp1 ψ
  have hweighted : AnalyticOnNhd ℂ (fun z : ℂ => z*f z)
      (closedBall (C.center n : ℂ) (C.radius n)) :=
    fun z hz => analyticAt_id.mul (hana z (C.closedBall_subset_original n hz))
  have hr : 0 ≤ C.radius n := ((C.inner_pos n).trans (C.inner_lt n)).le
  have hzero : (∮ z in C((C.center n : ℂ),C.radius n), z*f z) = 0 :=
    (hweighted.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hr
  have hsame : (∮ z in C((C.center n : ℂ),C.radius n), z*sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
      ∮ z in C((C.center n : ℂ),C.radius n), z*f z := by
    apply circleIntegral.integral_congr hr
    intro z hz
    have hzroot := C.collar_subset_rootDomain hD ψ hψU n (C.sphere_subset_collar n hz)
    exact congrArg (z*·) (Hc.agreement ψ hψ z hzroot).symm
  rw [C.indexedAction_eq_circle hD ψ hψU n,sourceActionCircle,hsame,hzero,mul_zero]

end NLS.ZakharovShabat
