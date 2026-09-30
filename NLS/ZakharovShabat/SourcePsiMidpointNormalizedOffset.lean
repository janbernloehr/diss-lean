import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset

/-!
# Index-independent offset estimates from a midpoint-normalized quotient

Rescale chi by its midpoint denominator. The resulting factor has
the same zero weighted period, but its midpoint value is exactly the
regular quotient. On a separated contour disc its norm is controlled
by the quotient bound and the disc geometry, independently of the
omitted index. The quadratic reciprocal-root correction then gives
a squared-gap offset bound, also for collapsed gaps.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiMidpointNormalizedRegularFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ m)*
    sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))/
    (sourceStandardRootMidpoint hp hp1 ψ n-z)

theorem sourcePsiMidpointNormalizedRegularFactor_eq_scaled_chi
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiMidpointNormalizedRegularFactor hp hp1 n m a ψ z =
      ((sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ m)/
        ((Real.pi : ℂ)*((n-m : ℤ) : ℂ)*I))*
          sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z := by
  have hnm : ((n-m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hmn.symm
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold sourcePsiMidpointNormalizedRegularFactor sourcePsiMidpointFilledRegularFactor sourcePsiGapRegularFactor
  rw [displacedRoots_sourcePsiFillDeletedRoot_same]
  by_cases hz : sourceStandardRootMidpoint hp hp1 ψ n-z = 0
  · simp only [hz,div_zero,mul_zero]
  · field_simp [hπ,hnm,I_ne_zero,hz]

theorem sourcePsiMidpointNormalizedRegularFactor_midpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hne : sourceStandardRootMidpoint hp hp1 ψ n ≠ sourceStandardRootMidpoint hp hp1 ψ m) :
    sourcePsiMidpointNormalizedRegularFactor hp hp1 n m a ψ (sourceStandardRootMidpoint hp hp1 ψ m) =
      sourceSingleRootQuotientJointProduct hp hp1 m
        (sourceStandardRootMidpoint hp hp1 ψ m,
          (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ)) := by
  unfold sourcePsiMidpointNormalizedRegularFactor
  rw [mul_comm,mul_div_cancel_right₀ _ (sub_ne_zero.mpr hne)]

theorem norm_sourcePsiMidpointNormalizedRegularFactor_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ)
    (d A M : ℝ) (hd : 0 < d) (hA : 0 ≤ A)
    (hden : d ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hmid : ‖z-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ A)
    (hQ : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖ ≤ M) :
    ‖sourcePsiMidpointNormalizedRegularFactor hp hp1 n m a ψ z‖ ≤ (1+A/d)*M := by
  let τn := sourceStandardRootMidpoint hp hp1 ψ n
  let τm := sourceStandardRootMidpoint hp hp1 ψ m
  have hdenpos : 0 < ‖τn-z‖ := hd.trans_le hden
  have htri : ‖τn-τm‖ ≤ ‖τn-z‖+A := by
    calc
      ‖τn-τm‖ = ‖(τn-z)+(z-τm)‖ := by congr 1; ring
      _ ≤ ‖τn-z‖+‖z-τm‖ := norm_add_le _ _
      _ ≤ ‖τn-z‖+A := add_le_add le_rfl hmid
  have hratio : ‖τn-τm‖/‖τn-z‖ ≤ 1+A/d := by
    calc
      _ ≤ (‖τn-z‖+A)/‖τn-z‖ := div_le_div_of_nonneg_right htri hdenpos.le
      _ = 1+A/‖τn-z‖ := by field_simp [hdenpos.ne']
      _ ≤ 1+A/d := add_le_add le_rfl (div_le_div_of_nonneg_left hA hd hden)
  rw [sourcePsiMidpointNormalizedRegularFactor,norm_div,norm_mul,mul_div_right_comm]
  exact mul_le_mul hratio hQ (norm_nonneg _) (by positivity)

/-- A separated disc and uniform quotient bounds give a quadratic
psi offset estimate with no index-dependent multiplier. -/
theorem norm_sourcePsi_midpointNormalized_root_offset_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ c R = 0)
    (hQanalytic : AnalyticOnNhd ℂ (fun z => sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))) (closedBall c R))
    (d sep A S M c₀ : ℝ) (hd : 0 < d) (hsepPos : 0 < sep)
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hM : 0 ≤ M) (hc₀ : 0 < c₀)
    (hden : ∀ z ∈ closedBall c R, d ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hmid : ∀ z ∈ closedBall c R, ‖z-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤ A)
    (hsep : ∀ z ∈ sphere c R, sep ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ sep)
    (hσ : ∀ z ∈ sphere c R, ‖displacedRoots (a : Coeff p) m-z‖ ≤ S)
    (hQbound : ∀ z ∈ closedBall c R, ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖ ≤ M)
    (hQlower : c₀ ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (sourceStandardRootMidpoint hp hp1 ψ m,
        (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))‖) :
    ‖displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
      (R*S/(sep^3*c₀))*(1+A/d)*M*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  let f := sourcePsiMidpointNormalizedRegularFactor hp hp1 n m a ψ
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let T := (1+A/d)*M
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hτ : τ ∈ closedBall c R :=
    ball_subset_closedBall (hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
  have hne z (hz : z ∈ closedBall c R) : sourceStandardRootMidpoint hp hp1 ψ n-z ≠ 0 :=
    norm_pos_iff.mp (hd.trans_le (hden z hz))
  have hf : AnalyticOnNhd ℂ f (closedBall c R) := by
    intro z hz
    exact (analyticAt_const.mul (hQanalytic z hz)).div
      (analyticAt_const.sub analyticAt_id) (hne z hz)
  have havoid z (hz : z ∈ sphere c R) : z ≠ sourceStandardRootMidpoint hp hp1 ψ n :=
    (sub_ne_zero.mp (hne z (sphere_subset_closedBall hz))).symm
  have hχzero := sourcePsiMidpointFilledRegularFactor_zero_period hp hp1 n m hmn a ψ c R hR.le hcircle havoid hzero
  let k := (sourceStandardRootMidpoint hp hp1 ψ n-τ)/((Real.pi : ℂ)*((n-m : ℤ) : ℂ)*I)
  have hperiod : (∮ z in C(c,R), ((displacedRoots (a : Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0 := by
    have heq : (fun z => ((displacedRoots (a : Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*f z) =
        (fun z => k*(((displacedRoots (a : Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*
          sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z)) := by
      funext z
      dsimp only [f]
      rw [sourcePsiMidpointNormalizedRegularFactor_eq_scaled_chi hp hp1 n m hmn a ψ z]
      ring
    rw [heq,circleIntegral.integral_const_mul,hχzero,mul_zero]
  have hbound z (hz : z ∈ closedBall c R) : ‖f z‖ ≤ T :=
    norm_sourcePsiMidpointNormalizedRegularFactor_le hp hp1 n m a ψ z d A M hd hA (hden z hz) (hmid z hz) (hQbound z hz)
  have hdev z (hz : z ∈ sphere c R) : ‖f z-f τ‖ ≤ 2*T := by
    exact (norm_sub_le _ _).trans (by linarith [hbound z (sphere_subset_closedBall hz),hbound τ hτ])
  have hlower : c₀ ≤ ‖f τ‖ := by
    dsimp only [f,τ]
    rw [sourcePsiMidpointNormalizedRegularFactor_midpoint hp hp1 n m a ψ (sub_ne_zero.mp (hne τ hτ))]
    exact hQlower
  have h := norm_sourceStandardRoot_zero_period_offset_le hp hp1 ψ m c
    (displacedRoots (a : Coeff p) m) R hR hseg f hf hperiod sep S (2*T) c₀
    hsepPos hS (by positivity) hc₀ hsep hgap hσ hdev hlower
  convert h using 1
  dsimp only [T]
  ring

end NLS.ZakharovShabat
