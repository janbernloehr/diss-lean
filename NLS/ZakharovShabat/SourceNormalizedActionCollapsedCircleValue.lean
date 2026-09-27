import NLS.ZakharovShabat.SourceNormalizedActionGlued
import NLS.ZakharovShabat.SourceNormalizedActionFactorContinuity
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Value of the normalized contour candidate at a collapsed gap

At zero squared gap, the rationalized selected-root kernel is a
Cauchy kernel plus a constant. The constant integrates to zero
against the deleted factor, leaving its midpoint value with the
coefficient prescribed by the cosine model.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized-action kernel at a collapsed gap is a Cauchy
kernel plus a holomorphic constant term. -/
theorem normalizedActionCircleKernel_zeroGap
    (τ B z : ℂ) (hτz : τ ≠ z) :
    normalizedActionCircleKernel τ 0 B z =
      -(1/8:ℂ)*(z-τ)⁻¹ + 2*B := by
  have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτz
  unfold normalizedActionCircleKernel
  simp only [normalizedStandardRoot_zeroGap, zero_mul, add_zero]
  field_simp
  ring

/-- At a collapsed gap, the fixed-circle normalized candidate is
exactly one quarter of `I` times the deleted factor at the periodic
midpoint. This formula is independent of the critical coefficient. -/
theorem normalizedActionCircleQuotient_zeroGap
    (τ B c : ℂ) (R : ℝ) (E : ℂ → ℂ)
    (hR : 0 < R) (hτ : τ ∈ ball c R)
    (hE : AnalyticOnNhd ℂ E (closedBall c R)) :
    normalizedActionCircleQuotient τ 0 B c R E = I*E τ/4 := by
  let C : ℂ → ℂ := fun z => (z-τ)⁻¹ * E z
  let H : ℂ → ℂ := fun z => E z
  have hτsphere : ∀ z ∈ sphere c R, z ≠ τ := by
    intro z hz he
    have hlt := mem_ball.mp hτ
    have heq := mem_sphere.mp hz
    rw [he] at heq
    exact (ne_of_lt hlt) heq
  have hCcont : ContinuousOn C (sphere c R) := by
    have hinv : ContinuousOn (fun z : ℂ => (z-τ)⁻¹) (sphere c R) := by
      apply ContinuousOn.inv₀
      · exact (continuousOn_id.sub continuousOn_const)
      · intro z hz
        exact sub_ne_zero.mpr (hτsphere z hz)
    exact hinv.mul (hE.continuousOn.mono sphere_subset_closedBall)
  have hCint : CircleIntegrable C c R :=
    hCcont.circleIntegrable hR.le
  have hHint : CircleIntegrable H c R :=
    (hE.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hCauchy : (∮ z in C(c,R), C z) = 2*(Real.pi:ℂ)*I*E τ := by
    simpa only [C, smul_eq_mul] using
      (hE.differentiableOn.circleIntegral_sub_inv_smul hτ)
  have hzero : (∮ z in C(c,R), H z) = 0 :=
    (hE.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le
  have hsame : (∮ z in C(c,R),
      normalizedActionCircleKernel τ 0 B z * E z) =
      ∮ z in C(c,R), -(1/8:ℂ)*C z + (2*B)*H z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have h := normalizedActionCircleKernel_zeroGap τ B z (Ne.symm (hτsphere z hz))
    dsimp [C,H]
    rw [h]
    ring
  unfold normalizedActionCircleQuotient
  rw [hsame, circleIntegral.integral_add]
  · rw [circleIntegral.integral_const_mul, circleIntegral.integral_const_mul,
      hCauchy,hzero]
    have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  · have hs := hCint.const_smul (a := -(1/8:ℂ))
    change CircleIntegrable (fun z => -(1/8:ℂ) • C z) c R at hs
    simpa only [smul_eq_mul] using hs
  · have hs := hHint.const_smul (a := (2*B))
    change CircleIntegrable (fun z => (2*B) • H z) c R at hs
    simpa only [smul_eq_mul] using hs

/-- The source contour candidate at a collapsed gap has the same
midpoint value as the real-type cosine limit. -/
theorem sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R)) :
    sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
      sourceNormalizedActionCollapsedCandidate hp hp1 n ψ := by
  let τ := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let B := canonicalCriticalGapQuotient hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hτ : τ ∈ ball c R :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have h := normalizedActionCircleQuotient_zeroGap τ B c R E hR hτ hE
  simpa only [sourceNormalizedActionCircleCandidate,
    sourceNormalizedActionCollapsedCandidate, sourceStandardRootMidpoint,
    hgap, zero_pow (by norm_num : (2:ℕ) ≠ 0), τ, B, E] using h

/-- On one complex neighborhood, the contour candidate fills the
raw quotient with precisely the already prescribed collapsed value.
Its restriction to real-type sources is the established continuous
real normalized-action extension. -/
theorem exists_local_sourceNormalizedActionCircleCandidate_eq_realExtension
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        DifferentiableOn ℂ
          (sourceNormalizedActionCircleCandidate hp hp1 n c R) U ∧
        ∀ ψ ∈ U,
          (sourceComplexAction hp hp1 n ψ =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
              sourceNormalizedActionCircleCandidate hp hp1 n c R ψ) ∧
          (sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
            sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
              sourceNormalizedActionCollapsedCandidate hp hp1 n ψ) ∧
          (IsRealType (CoeffPair.toMax p ψ) →
            sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
              sourceNormalizedActionRealExtension hp hp1 n ψ) := by
  obtain ⟨V,hVopen,hφV,c,R,hR,hgeom,hdiff,_,hfactor⟩ :=
    exists_local_sourceComplexAction_normalizedCircleCandidate hp hp1 φ hφ n
  obtain ⟨W,hWopen,hrealW,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  let U := V ∩ W
  have hUopen : IsOpen U := hVopen.inter hWopen
  have hφU : φ ∈ U := ⟨hφV,hrealW hφ⟩
  refine ⟨U,hUopen,hφU,c,R,hR,hdiff.mono inter_subset_left,?_⟩
  intro ψ hψ
  have hcollapsed (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
      sourceNormalizedActionCircleCandidate hp hp1 n c R ψ =
        sourceNormalizedActionCollapsedCandidate hp hp1 n ψ := by
    obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1
    have hE : AnalyticOnNhd ℂ
        (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
      intro z hz
      exact hEdata ψ hψ.2 n z (hother hz)
    exact sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero
      hp hp1 ψ n c R hR hgap hseg hE
  refine ⟨(hfactor ψ hψ.1).1,hcollapsed,?_⟩
  intro hψreal
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · simpa only [sourceNormalizedActionRealExtension, if_pos hgap] using
      (hcollapsed hgap)
  · have hraw := (hfactor ψ hψ.1).2 (pow_ne_zero 2 hgap)
    simpa only [sourceNormalizedActionRealExtension, if_neg hgap] using
      hraw.symm

end NLS.ZakharovShabat
