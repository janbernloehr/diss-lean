import NLS.ZakharovShabat.SourceAngularEndpointBound
import NLS.ZakharovShabat.SourceAngularAnnulusPrimitive
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle

/-!
# Removing the exact diagonal eta period

The explicit differential `i / standardRoot` has the same `2π` period
as the actual normalized diagonal angular differential. Their difference
has an analytic regular numerator and zero period. These statements hold
at every complex source, including collapsed gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit differential carrying the diagonal eta period. -/
def sourceAngularEtaModelIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  Complex.I / sourceStandardRoot hp hp1 ψ n z

/-- The actual diagonal differential with its normalized period removed. -/
def sourceAngularEtaRemainderIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ) -
    sourceAngularEtaModelIntegrand hp hp1 n ψ z

/-- Subtracting the constant `i` from the regular numerator gives
the exact remainder, with no division assumptions. -/
theorem sourceAngularEtaRemainderIntegrand_eq_gapNumerator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ) :
    sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z =
      (sourceAngularGapNumerator hp hp1 n n s ψ z-Complex.I) /
        sourceStandardRoot hp hp1 ψ n z := by
  unfold sourceAngularEtaRemainderIntegrand sourceAngularEtaModelIntegrand
  rw [sourceAngularIntegrand_eq_gapNumerator_div_standardRoot hp hp1 n n s ψ z]
  exact (sub_div _ _ _).symm

theorem sourceAngularEtaModelIntegrand_analyticAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (sourceAngularEtaModelIntegrand hp hp1 n ψ) z := by
  change AnalyticAt ℂ (fun w => Complex.I / sourceStandardRoot hp hp1 ψ n w) z
  simp only [div_eq_mul_inv]
  have h := (analyticAt_const (v := Complex.I)).mul
    (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z hz)
  change AnalyticAt ℂ (fun w : ℂ => Complex.I * (sourceStandardRoot hp hp1 ψ n w)⁻¹) z at h
  exact h

/-- Holomorphy up to the enclosing circle on the entire cut complement. -/
theorem sourceAngularEtaRemainderIntegrand_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ)
    (hother : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    AnalyticOnNhd ℂ (sourceAngularEtaRemainderIntegrand hp hp1 n s ψ)
      (closedBall c R \ sourcePeriodicSegment hp hp1 ψ n) := by
  intro z hz
  have hcanonical : z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro m
    by_cases hmn : m = n
    · subst m; exact hz.2
    · exact (hother hz.1) m hmn
  exact (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ
    z hcanonical).sub (sourceAngularEtaModelIntegrand_analyticAt hp hp1 n ψ z hz.2)

/-- The explicit model has raw contour period `2π` on any enclosing
circle, for an arbitrary complex or collapsed periodic gap. -/
theorem circleIntegral_sourceAngularEtaModelIntegrand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r) :
    (∮ z in C(c,r), sourceAngularEtaModelIntegrand hp hp1 n ψ z) = 2*Real.pi := by
  simp only [sourceAngularEtaModelIntegrand,div_eq_mul_inv,
    circleIntegral.integral_const_mul]
  rw [circleIntegral_sourceStandardRoot_inv_of_gap_mem_ball hp hp1 ψ n c r hr hgap]
  calc
    Complex.I * -(2*(Real.pi : ℂ)*Complex.I) = -(2*(Real.pi : ℂ))*(Complex.I*Complex.I) := by ring
    _ = 2*Real.pi := by rw [I_mul_I]; ring

/-- The actual normalized diagonal contour cancels the model exactly. -/
theorem circleIntegral_sourceAngularEtaRemainderIntegrand_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r)
    (hother : closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hperiod : sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ c r = 1) :
    (∮ z in C(c,r), sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z) = 0 := by
  let f : ℂ → ℂ := fun z => sourceAngularIntegrand n s
    (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ)
  have havoid z (hz : z ∈ sphere c r) : z ∉ sourcePeriodicSegment hp hp1 ψ n := by
    intro hzin
    exact (ne_of_lt (mem_ball.mp (hgap hzin))) (mem_sphere.mp hz)
  have hf : ContinuousOn f (sphere c r) := by
    apply (analyticOnNhd_sourcePsiContourIntegrand_fixed hp hp1 n (s n ψ : Coeff p) ψ).continuousOn.mono
    intro z hz m
    by_cases hmn : m = n
    · subst m; exact havoid z hz
    · exact (hother (sphere_subset_closedBall hz)) m hmn
  have hmodel : ContinuousOn (sourceAngularEtaModelIntegrand hp hp1 n ψ) (sphere c r) := by
    intro z hz
    exact (sourceAngularEtaModelIntegrand_analyticAt hp hp1 n ψ z
      (havoid z hz)).continuousAt.continuousWithinAt
  have hraw : (∮ z in C(c,r), f z) = 2*Real.pi := by
    change (2*Real.pi : ℂ)⁻¹ * (∮ z in C(c,r), f z) = 1 at hperiod
    have hne : (2*Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have heq := congrArg (fun w : ℂ => (2*Real.pi : ℂ)*w) hperiod
    simpa only [← mul_assoc,mul_inv_cancel₀ hne,one_mul,mul_one] using heq
  change (∮ z in C(c,r), f z-sourceAngularEtaModelIntegrand hp hp1 n ψ z) = 0
  rw [circleIntegral.integral_sub (hf.circleIntegrable hr.le) (hmodel.circleIntegrable hr.le),
    hraw,circleIntegral_sourceAngularEtaModelIntegrand hp hp1 n ψ c r hr hgap,sub_self]

end NLS.ZakharovShabat
