import NLS.ZakharovShabat.SourceStandardRootGapSideSource
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle
import NLS.ZakharovShabat.SourceStandardRootContourLocalStability
import NLS.ComplexAnalysis.CircleIntegralIntegrationByParts

/-!
# The first weighted moment of the standard root

The standard root satisfies a quadratic equation off its gap.
Differentiating it shows that `(z-τ)/w(z)` is the derivative of
`w(z)`. Its integral around any gap-avoiding closed circle vanishes,
without needing analyticity inside the filled circle. Together with
the diagonal inverse-root integral, this gives the affine case of the
weighted contour estimate in Lemma 12.3.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The derivative of the standard root off the selected gap is its
centered spectral coordinate divided by the root. -/
theorem deriv_sourceStandardRoot_off_segment
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (z : ℂ) (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    deriv (sourceStandardRoot hp hp1 ψ n) z =
      (z-sourceStandardRootMidpoint hp hp1 ψ n) /
        sourceStandardRoot hp hp1 ψ n z := by
  let w : ℂ → ℂ := sourceStandardRoot hp hp1 ψ n
  let a : ℂ := canonicalPeriodicLeft hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let b : ℂ := canonicalPeriodicRight hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hw : DifferentiableAt ℂ w z :=
    (sourceStandardRoot_analyticAt hp hp1 ψ n z hz).differentiableAt
  have hwne : w z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz
  let L : ℂ → ℂ := (fun _ => a)-id
  let R : ℂ → ℂ := (fun _ => b)-id
  have hsq : w*w =ᶠ[𝓝 z] L*R := by
    filter_upwards [((isClosed_sourcePeriodicSegment hp hp1 ψ n).isOpen_compl).mem_nhds hz]
      with u hu
    change w u*w u = (a-u)*(b-u)
    simpa only [pow_two] using
      sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n u hu
  have hleft : HasDerivAt (w*w)
      (deriv w z*w z + w z*deriv w z) z :=
    hw.hasDerivAt.mul hw.hasDerivAt
  have hright : HasDerivAt (L*R)
      ((0-1)*R z+L z*(0-1)) z :=
    ((hasDerivAt_const z a).sub (hasDerivAt_id z)).mul
      ((hasDerivAt_const z b).sub (hasDerivAt_id z))
  have hderiv : 2*w z*deriv w z = 2*z-(a+b) := by
    have heq := hsq.deriv_eq
    rw [hleft.deriv, hright.deriv] at heq
    dsimp [L,R] at heq
    linear_combination heq
  have hmid : sourceStandardRootMidpoint hp hp1 ψ n = (a+b)/2 := rfl
  rw [hmid]
  apply (eq_div_iff hwne).2
  linear_combination (1/2:ℂ) * hderiv

/-- The first centered inverse-root moment vanishes on every circle
that avoids the selected gap. The root itself is its primitive. -/
theorem circleIntegral_sourceStandardRoot_centered_inv_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ) :
    (∮ z in C(c,R),
      (z-sourceStandardRootMidpoint hp hp1 ψ n) /
        sourceStandardRoot hp hp1 ψ n z) = 0 := by
  have hzero : (∮ z in C(c,R),
      deriv (sourceStandardRoot hp hp1 ψ n) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR
    intro z hz
    exact ((sourceStandardRoot_analyticAt hp hp1 ψ n z
      (hcircle hz)).differentiableAt.hasDerivAt).hasDerivWithinAt
  rw [← hzero]
  apply circleIntegral.integral_congr hR
  intro z hz
  exact (deriv_sourceStandardRoot_off_segment hp hp1 ψ n z
    (hcircle hz)).symm

/-- The circle integral of an affine numerator over the selected
standard root depends only on its value at the periodic midpoint. -/
theorem circleIntegral_affine_div_sourceStandardRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R) :
    (∮ z in C(c,R), (σ-z) / sourceStandardRoot hp hp1 ψ n z) =
      -(2*Real.pi*I) *
        (σ-sourceStandardRootMidpoint hp hp1 ψ n) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let w := sourceStandardRoot hp hp1 ψ n
  have hcircle : sphere c R ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    intro z hz hmem
    have hlt := mem_ball.mp (hseg hmem)
    have heq := mem_sphere.mp hz
    exact (ne_of_lt hlt) heq
  have hinvCont : ContinuousOn (fun z => (w z)⁻¹) (sphere c R) := by
    intro z hz
    exact ((sourceStandardRoot_inv_analyticAt hp hp1 ψ n z
      (hcircle hz)).continuousAt).continuousWithinAt
  have hinvInt : CircleIntegrable (fun z => (w z)⁻¹) c R :=
    hinvCont.circleIntegrable hR.le
  have hcenterInt : CircleIntegrable
      (fun z => (z-τ)/(w z)) c R := by
    have hcont : ContinuousOn (fun z => (z-τ)*(w z)⁻¹)
        (sphere c R) :=
      (continuousOn_id.sub continuousOn_const).mul hinvCont
    simpa only [div_eq_mul_inv] using hcont.circleIntegrable hR.le
  have hconstInt : CircleIntegrable
      (fun z => (σ-τ)*(w z)⁻¹) c R := by
    have h := hinvInt.const_smul (a := σ-τ)
    change CircleIntegrable (fun z => (σ-τ)*(w z)⁻¹) c R at h
    exact h
  have hsame : (∮ z in C(c,R), (σ-z)/(w z)) =
      ∮ z in C(c,R), (σ-τ)*(w z)⁻¹ - (z-τ)/(w z) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hw : w z ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hcircle hz)
    field_simp [hw]
    ring
  rw [hsame, circleIntegral.integral_sub hconstInt hcenterInt]
  rw [circleIntegral.integral_const_mul,
    circleIntegral_sourceStandardRoot_centered_inv_eq_zero
      hp hp1 ψ n c R hR.le hcircle,
    circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball
      hp hp1 ψ n c R hR hseg]
  dsimp [w,τ]
  ring

/-- The affine case of the gap maximum estimate from Lemma 12.3:
the normalized contour is bounded by the maximum of the affine
numerator on the gap segment. -/
theorem norm_circleIntegral_affine_div_sourceStandardRoot_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R)
    (M : ℝ) (hM : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      ‖σ-z‖ ≤ M) :
    ‖(2*Real.pi : ℂ)⁻¹ *
      (∮ z in C(c,R), (σ-z)/sourceStandardRoot hp hp1 ψ n z)‖ ≤ M := by
  rw [circleIntegral_affine_div_sourceStandardRoot hp hp1 ψ n c σ R hR hseg]
  have hπ : (2*Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hnorm : ‖(2*Real.pi : ℂ)⁻¹ *
      (-(2*Real.pi*I) *
        (σ-sourceStandardRootMidpoint hp hp1 ψ n))‖ =
      ‖σ-sourceStandardRootMidpoint hp hp1 ψ n‖ := by
    field_simp [hπ]
    simp
  rw [hnorm]
  exact hM _ (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)

end NLS.ZakharovShabat
