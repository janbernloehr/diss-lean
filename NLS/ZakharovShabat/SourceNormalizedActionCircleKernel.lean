import NLS.ZakharovShabat.SourceActionCircle
import NLS.ZakharovShabat.SourceStandardRootAlgebra
import NLS.ZakharovShabat.SourceCriticalRootRatioFactorization
import NLS.ZakharovShabat.SourceCriticalOffsetCoefficientNonzero

/-!
# An algebraic kernel for the normalized action

The selected critical point has the form `τ + γ² B`. On an isolating
circle, its recentered action integrand is the sum of a holomorphic
term and `γ²` times an explicit kernel. This identity does not divide
by `γ²` and therefore also applies at collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The gap-independent kernel obtained by rationalizing the selected
standard root in the recentered action integrand. -/
def normalizedActionCircleKernel (τ q B z : ℂ) : ℂ :=
  let d := τ-z
  let w := normalizedStandardRoot τ q z
  (d/(4*(d+w)) + 2*d*B + q*B^2)/w

/-- Rationalizing the normalized root never creates a new zero
away from the periodic midpoint. -/
theorem normalizedStandardRoot_add_ne_zero (τ q z : ℂ) (hτ : τ ≠ z) :
    τ-z+normalizedStandardRoot τ q z ≠ 0 := by
  by_cases hq : q = 0
  · rw [hq, normalizedStandardRoot_zeroGap]
    have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτ
    have htwo : (2:ℂ)*(τ-z) ≠ 0 := mul_ne_zero (by norm_num) hd
    simpa only [two_mul] using htwo
  · intro hzero
    have hw : normalizedStandardRoot τ q z = -(τ-z) := by
      linear_combination hzero
    have hsq := normalizedStandardRoot_sq τ q z hτ
    rw [hw] at hsq
    have : q = 0 := by linear_combination 4 * hsq
    exact hq this

/-- The rationalized kernel is analytic wherever the selected root
is analytic and nonzero. -/
theorem normalizedActionCircleKernel_analyticAt
    (τ q B z : ℂ)
    (hroot : AnalyticAt ℂ (normalizedStandardRoot τ q) z)
    (hrootne : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    AnalyticAt ℂ (normalizedActionCircleKernel τ q B) z := by
  have hd : AnalyticAt ℂ (fun w : ℂ => τ-w) z :=
    analyticAt_const.sub analyticAt_id
  have hsum : AnalyticAt ℂ
      (fun w : ℂ => 4*(τ-w+normalizedStandardRoot τ q w)) z :=
    analyticAt_const.mul (hd.add hroot)
  have hsumne : (4:ℂ)*(τ-z+normalizedStandardRoot τ q z) ≠ 0 :=
    mul_ne_zero (by norm_num) hplus
  change AnalyticAt ℂ (fun w : ℂ =>
    ((τ-w)/(4*(τ-w+normalizedStandardRoot τ q w)) +
      2*(τ-w)*B+q*B^2)/normalizedStandardRoot τ q w) z
  exact (((hd.div hsum hsumne).add
    ((analyticAt_const.mul hd).mul analyticAt_const)).add analyticAt_const).div
      hroot hrootne

/-- The integrand identity behind division of the action by the
squared gap. The only denominators are spectral denominators on the
isolating circle, never the squared gap itself. -/
theorem normalizedActionCircleKernel_identity
    (τ q B z : ℂ) (hτ : τ ≠ z)
    (hw : normalizedStandardRoot τ q z ≠ 0)
    (hplus : τ-z+normalizedStandardRoot τ q z ≠ 0) :
    -((τ+q*B-z)^2 / normalizedStandardRoot τ q z) =
      -(τ-z) - q*normalizedActionCircleKernel τ q B z := by
  have hsq := normalizedStandardRoot_sq τ q z hτ
  unfold normalizedActionCircleKernel
  dsimp only
  field_simp
  linear_combination 4 * (τ-z) * hsq

/-- A fixed-circle candidate for the action divided by the squared
gap. Its definition remains meaningful when the gap is zero. -/
def normalizedActionCircleQuotient (τ q B c : ℂ) (R : ℝ) (E : ℂ → ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ *
    ∮ z in C(c,R), normalizedActionCircleKernel τ q B z * E z

/-- The recentered action integral factors through the squared gap.
The only analytic input is that the deleted factor extends across
the filled isolating circle. -/
theorem normalizedActionCircle_integral_factor
    (τ q B c : ℂ) (R : ℝ) (E : ℂ → ℂ)
    (hR : 0 ≤ R)
    (hE : AnalyticOnNhd ℂ E (closedBall c R))
    (hK : CircleIntegrable
      (fun z => normalizedActionCircleKernel τ q B z * E z) c R)
    (hden : ∀ z ∈ sphere c R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0) :
    (Real.pi : ℂ)⁻¹ *
      (∮ z in C(c,R),
        -((τ+q*B-z)^2 / normalizedStandardRoot τ q z) * E z) =
      q * normalizedActionCircleQuotient τ q B c R E := by
  let H : ℂ → ℂ := fun z => -(τ-z) * E z
  let K : ℂ → ℂ := fun z => normalizedActionCircleKernel τ q B z * E z
  have hH : AnalyticOnNhd ℂ H (closedBall c R) := by
    intro z hz
    exact (analyticAt_const.sub analyticAt_id).neg.mul (hE z hz)
  have hHintegrable : CircleIntegrable H c R :=
    (hH.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR
  have hzero : (∮ z in C(c,R), H z) = 0 :=
    (hH.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR
  have heq :
      (∮ z in C(c,R),
        -((τ+q*B-z)^2 / normalizedStandardRoot τ q z) * E z) =
      (∮ z in C(c,R), H z - q*K z) := by
    apply circleIntegral.integral_congr hR
    intro z hz
    have h := normalizedActionCircleKernel_identity τ q B z
      (hden z hz).1 (hden z hz).2.1 (hden z hz).2.2
    dsimp [H,K]
    rw [h]
    ring
  change CircleIntegrable K c R at hK
  have hqK : CircleIntegrable (fun z => q*K z) c R := by
    have hs := hK.const_smul (a := q)
    change CircleIntegrable (fun z => q • K z) c R at hs
    simpa only [smul_eq_mul] using hs
  rw [heq, circleIntegral.integral_sub hHintegrable hqK]
  rw [hzero, circleIntegral.integral_const_mul]
  unfold normalizedActionCircleQuotient
  ring

/-- For the actual Zakharov–Shabat action, the kernel formula applies
whenever a fixed circle isolates the selected gap and the deleted
factor is analytic in its filled disc. -/
theorem sourceActionCircle_eq_squaredGap_mul_kernel
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (a : ℂ) (R : ℝ) (B : ℂ) (hR : 0 ≤ R)
    (hcircle : sphere a R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzseg : ∀ z ∈ sphere a R,
      z ∉ sourcePeriodicSegment hp hp1 ψ n)
    (hzero : (∮ z in C(a,R),
      sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0)
    (hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall a R))
    (hoffset :
      canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 * B) :
    sourceActionCircle hp hp1 ψ a R =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
        normalizedActionCircleQuotient
          (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n)
          ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2) B a R
          (sourceCriticalRootRatioExtension hp hp1 n ψ) := by
  let τ := canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let q := (sourcePeriodicGapDisplacement hp hp1 ψ n)^2
  let b := canonicalCriticalPoints hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  have hroot (z : ℂ) :
      sourceStandardRoot hp hp1 ψ n z = normalizedStandardRoot τ q z := by
    simp only [sourceStandardRoot, τ, q, sourcePeriodicGapDisplacement_apply]
  have hb : b = τ+q*B := by
    linear_combination hoffset
  have hrewrite :
      sourceActionCircle hp hp1 ψ a R =
        (Real.pi : ℂ)⁻¹ *
          (∮ z in C(a,R),
            -((τ+q*B-z)^2 / normalizedStandardRoot τ q z) * E z) := by
    rw [sourceActionCircle_eq_recentered hp hp1 ψ a R hR hcircle hzero b]
    congr 1
    apply circleIntegral.integral_congr hR
    intro z hz
    have hfactor := sourceCriticalRootRatio_eq_selectedFactor_mul_extension
      hp hp1 ψ n z (hcircle hz)
    change sourceCriticalRootRatioJoint hp hp1 (z,ψ) =
      ((b-z)/sourceStandardRoot hp hp1 ψ n z)*E z at hfactor
    change (z-b)*sourceCriticalRootRatioJoint hp hp1 (z,ψ) = _
    rw [hfactor, hb, hroot]
    ring
  have hden : ∀ z ∈ sphere a R,
      τ ≠ z ∧ normalizedStandardRoot τ q z ≠ 0 ∧
        τ-z+normalizedStandardRoot τ q z ≠ 0 := by
    intro z hz
    have hτ : τ ≠ z := by
      intro he
      exact hzseg z hz (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
    have hw : normalizedStandardRoot τ q z ≠ 0 := by
      rw [← hroot]
      exact sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hzseg z hz)
    exact ⟨hτ,hw,normalizedStandardRoot_add_ne_zero τ q z hτ⟩
  have hK : CircleIntegrable (fun z =>
      normalizedActionCircleKernel τ q B z * E z) a R := by
    apply ContinuousOn.circleIntegrable hR
    intro z hz
    have hrootfun : (normalizedStandardRoot τ q) =
        sourceStandardRoot hp hp1 ψ n := by
      funext w
      exact (hroot w).symm
    have hanroot : AnalyticAt ℂ (normalizedStandardRoot τ q) z := by
      rw [hrootfun]
      exact sourceStandardRoot_analyticAt hp hp1 ψ n z (hzseg z hz)
    have hanK := normalizedActionCircleKernel_analyticAt τ q B z
      hanroot (hden z hz).2.1 (hden z hz).2.2
    exact (hanK.mul (hE z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  rw [hrewrite]
  exact normalizedActionCircle_integral_factor τ q B a R E hR hE hK hden

/-- Every real-type source and selected index has a fixed circle and
one complex source neighborhood on which the action is exactly the
analytic squared gap times the rationalized contour candidate. The
identity includes complex sources with collapsed selected gaps. -/
theorem exists_local_sourceActionCircle_squaredGap_factor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        ∀ ψ ∈ V,
          sourceActionCircle hp hp1 ψ c R =
            (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
              normalizedActionCircleQuotient
                (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) n)
                ((sourcePeriodicGapDisplacement hp hp1 ψ n)^2)
                (canonicalCriticalGapQuotient hp hp1
                  (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
                c R (sourceCriticalRootRatioExtension hp hp1 n ψ) := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom,hzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_allGaps
      hp hp1 φ hφ n
  obtain ⟨W₁,hW₁open,hreal₁,hEdata⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  obtain ⟨W₂,hW₂open,_,hreal₂,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  let V := V₀ ∩ W₁ ∩ W₂
  have hVopen : IsOpen V := (hV₀open.inter hW₁open).inter hW₂open
  have hφV : φ ∈ V := ⟨⟨hφV₀,hreal₁ hφ⟩,hreal₂ hφ⟩
  refine ⟨V,hVopen,hφV,c,R,hR,?_⟩
  intro ψ hψ
  obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1.1
  have hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
  have hzseg : ∀ z ∈ sphere c R,
      z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro z hz
    exact hcircle hz n
  have hE : AnalyticOnNhd ℂ
      (sourceCriticalRootRatioExtension hp hp1 n ψ) (closedBall c R) := by
    intro z hz
    exact hEdata ψ hψ.1.2 n z (hother hz)
  exact sourceActionCircle_eq_squaredGap_mul_kernel hp hp1 ψ n c R
    (canonicalCriticalGapQuotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    hR.le hcircle hzseg (hzero ψ hψ.1.1) hE
    (hexact ψ hψ.2 n).2

end NLS.ZakharovShabat
