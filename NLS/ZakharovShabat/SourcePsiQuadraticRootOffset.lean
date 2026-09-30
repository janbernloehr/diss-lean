import NLS.ZakharovShabat.SourceStandardRootQuadraticOffset
import NLS.ZakharovShabat.SourcePsiFilledRegularFactor
import NLS.SequenceSpaces.SquaredWeightQuotient

/-!
# The actual psi root-offset equation of Lemma 12.12

Fill the unused root with its moving spectral midpoint, as in (2.31).
The weighted regular factor has precisely the actual retained contour
equation as its standard-root period. A zero period gives the exact
first-order identity (2.33) and a direct squared-gap offset estimate
from the factor's centered variation and midpoint lower bound.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The regular factor chi in (2.31), using the actual psi quotient
and the moving midpoint at the unused root index. -/
def sourcePsiMidpointFilledRegularFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (Real.pi : ℂ)*((n-m : ℤ) : ℂ)*sourcePsiGapRegularFactor hp hp1 n m
    (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)) ψ z

/-- Actual quotient analyticity and assigned-disc separation make chi
analytic on the selected filled contour disc. -/
theorem analyticOnNhd_sourcePsiMidpointFilledRegularFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (n m : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (U : Set (CoeffPair p)) (hψU : ψ ∈ U)
    (hQ : AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 U m)) (c : ℂ) (R : ℝ)
    (hdom : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hclosed : closedBall c R ⊆ sourceIsolatingDisc hp hp1 φ N ε m)
    (hmidn : sourceStandardRootMidpoint hp hp1 ψ n ∈ sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n)) :
    AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ) (closedBall c R) := by
  have hw := analyticOnNhd_sourcePsiFillDeletedRoot_gapRegularFactor hp hp1 φ N ε n m a
    (sourceStandardRootMidpoint hp hp1 ψ n) ψ U hψU hQ c R hdom hclosed hmidn hdisjoint
  intro z hz
  have h : AnalyticAt ℂ (fun w => (Real.pi : ℂ)*(((n-m : ℤ) : ℂ)*sourcePsiGapRegularFactor hp hp1 n m
      (sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)) ψ w)) z :=
    analyticAt_const.mul (hw z hz)
  convert h using 1
  funext w
  unfold sourcePsiMidpointFilledRegularFactor
  ring

/-- The literal period of chi is pi times the actual retained scalar
psi equation. Filling the omitted root leaves the numerator unchanged. -/
theorem sourcePsiMidpointFilledRegularFactor_period
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ sourceStandardRootMidpoint hp hp1 ψ n) :
    (∮ z in C(c,R), ((displacedRoots (a : Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*
      sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z) =
        (Real.pi : ℂ)*sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ c R := by
  let b := sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)
  have havoidb : ∀ z ∈ sphere c R, z ≠ displacedRoots b n := by
    simpa only [b,displacedRoots_sourcePsiFillDeletedRoot_same] using havoid
  have hF := sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral hp hp1 n m b ψ c R hR hcircle havoidb
  have hfill : sourcePsiEquationCoordinate hp hp1 n m b ψ c R =
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ c R := by
    exact sourcePsiEquationCoordinate_fillDeletedRoot hp hp1 n m a _ ψ c R hR
  rw [← hfill,hF,← mul_assoc,← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z _
  simp only [sourcePsiMidpointFilledRegularFactor,b,displacedRoots_sourcePsiFillDeletedRoot_other n m hmn]
  ring

/-- Retained contour orthogonality gives the zero period (2.30) for
the actual midpoint-filled factor, also at complex potentials. -/
theorem sourcePsiMidpointFilledRegularFactor_zero_period
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ sourceStandardRootMidpoint hp hp1 ψ n)
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ c R = 0) :
    (∮ z in C(c,R), ((displacedRoots (a : Coeff p) m-z)/sourceStandardRoot hp hp1 ψ m z)*
      sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z) = 0 := by
  rw [sourcePsiMidpointFilledRegularFactor_period hp hp1 n m hmn a ψ c R hR hcircle havoid]
  simp only [sourcePsiEquationCoordinate,hzero,mul_zero]

/-- Equation (2.33) for the actual psi root and midpoint-filled chi. -/
theorem sourcePsi_midpointFilled_dslope_identity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ sourceStandardRootMidpoint hp hp1 ψ n)
    (hf : AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ) (closedBall c R))
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ c R = 0) :
    (2*Real.pi*I : ℂ)*(displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m)*
      sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ (sourceStandardRootMidpoint hp hp1 ψ m) =
        ∮ z in C(c,R),
          ((displacedRoots (a : Coeff p) m-z)*(z-sourceStandardRootMidpoint hp hp1 ψ m)/
            sourceStandardRoot hp hp1 ψ m z)*
              dslope (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ)
                (sourceStandardRootMidpoint hp hp1 ψ m) z := by
  exact sourceStandardRoot_zero_period_dslope_identity hp hp1 ψ m c
    (displacedRoots (a : Coeff p) m) R hR hseg _ hf
    (sourcePsiMidpointFilledRegularFactor_zero_period hp hp1 n m hmn a ψ c R hR.le hcircle havoid hzero)

/-- A centered chi majorant and a positive midpoint lower bound give
the actual psi root a quadratic-gap offset estimate. The assumptions
are spectral geometry and factor bounds, not a root asymptotic. -/
theorem norm_sourcePsi_midpointFilled_root_offset_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere c R, z ≠ sourceStandardRootMidpoint hp hp1 ψ n)
    (hf : AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ) (closedBall c R))
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ c R = 0)
    (d S M c₀ : ℝ) (hd : 0 < d) (hS : 0 ≤ S) (hM : 0 ≤ M) (hc₀ : 0 < c₀)
    (hsep : ∀ z ∈ sphere c R, d ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ d)
    (hσ : ∀ z ∈ sphere c R, ‖displacedRoots (a : Coeff p) m-z‖ ≤ S)
    (hdev : ∀ z ∈ sphere c R,
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-
        sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ (sourceStandardRootMidpoint hp hp1 ψ m)‖ ≤ M)
    (hlower : c₀ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ
      (sourceStandardRootMidpoint hp hp1 ψ m)‖) :
    ‖displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
      (R*S/(2*d^3*c₀))*M*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  exact norm_sourceStandardRoot_zero_period_offset_le hp hp1 ψ m c
    (displacedRoots (a : Coeff p) m) R hR hseg _ hf
    (sourcePsiMidpointFilledRegularFactor_zero_period hp hp1 n m hmn a ψ c R hR.le hcircle havoid hzero)
    d S M c₀ hd hS hM hc₀ hsep hgap hσ hdev hlower

/-- On the actual free-centered tail geometry, chi's error from i
gives a squared-gap offset bound with a constant independent of both
spectral indices. The midpoint lower bound remains explicit. -/
theorem norm_sourcePsi_midpointFilled_tail_offset_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (hroot : ‖displacedRoots (a : Coeff p) m-(Real.pi : ℂ)*m‖ ≤ Real.pi/4)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8), z ≠ sourceStandardRootMidpoint hp hp1 ψ n)
    (hf : AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ)
      (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)))
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8) = 0)
    (M c₀ : ℝ) (hM : 0 ≤ M) (hc₀ : 0 < c₀)
    (herror : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ M)
    (hlower : c₀ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ
      (sourceStandardRootMidpoint hp hp1 ψ m)‖) :
    ‖displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
      (192/(Real.pi*c₀))*M*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  let c : ℂ := (Real.pi : ℂ)*m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let f := sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ
  have hseg := sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have hτ : τ ∈ closedBall c (Real.pi/8) :=
    ball_subset_closedBall (hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
  have hsep z (hz : z ∈ sphere c (Real.pi/8)) : Real.pi/16 ≤ ‖τ-z‖ := by
    have hzdist : ‖z-c‖ = Real.pi/8 := by simpa only [mem_sphere,dist_eq_norm] using hz
    have htri : ‖z-c‖ ≤ ‖z-τ‖+‖τ-c‖ := by
      calc
        ‖z-c‖ = ‖(z-τ)+(τ-c)‖ := by congr 1; ring
        _ ≤ ‖z-τ‖+‖τ-c‖ := norm_add_le _ _
    rw [hzdist,norm_sub_rev] at htri
    linarith [Real.pi_pos]
  have hσ z (hz : z ∈ sphere c (Real.pi/8)) : ‖displacedRoots (a : Coeff p) m-z‖ ≤ 3*Real.pi/8 := by
    have hzdist : ‖c-z‖ = Real.pi/8 := by simpa only [mem_sphere,dist_eq_norm,norm_sub_rev] using hz
    have htri : ‖displacedRoots (a : Coeff p) m-z‖ ≤
        ‖displacedRoots (a : Coeff p) m-c‖+‖c-z‖ := by
      calc
        ‖displacedRoots (a : Coeff p) m-z‖ =
            ‖(displacedRoots (a : Coeff p) m-c)+(c-z)‖ := by congr 1; ring
        _ ≤ ‖displacedRoots (a : Coeff p) m-c‖+‖c-z‖ := norm_add_le _ _
    rw [hzdist] at htri
    linarith
  have hdev z (hz : z ∈ sphere c (Real.pi/8)) : ‖f z-f τ‖ ≤ 2*M := by
    have h₁ := herror z (sphere_subset_closedBall hz)
    have h₂ := herror τ hτ
    have htri : ‖f z-f τ‖ ≤ ‖f z-I‖+‖I-f τ‖ := by
      calc
        ‖f z-f τ‖ = ‖(f z-I)+(I-f τ)‖ := by congr 1; ring
        _ ≤ ‖f z-I‖+‖I-f τ‖ := norm_add_le _ _
    rw [norm_sub_rev I] at htri
    linarith
  have h := norm_sourcePsi_midpointFilled_root_offset_le hp hp1 n m hmn a ψ c (Real.pi/8)
    (by positivity) hseg hcircle havoid hf hzero (Real.pi/16) (3*Real.pi/8) (2*M) c₀
    (by positivity) (by positivity) (by positivity) hc₀ hsep (by linarith [Real.pi_pos]) hσ hdev hlower
  convert h using 1
  field_simp
  ring

/-- In the small-error tail, the free value i gives the midpoint
lower bound automatically, so only the actual chi error is needed. -/
theorem norm_sourcePsi_midpointFilled_small_error_tail_offset_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m-(Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (hroot : ‖displacedRoots (a : Coeff p) m-(Real.pi : ℂ)*m‖ ≤ Real.pi/4)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere ((Real.pi : ℂ)*m) (Real.pi/8), z ≠ sourceStandardRootMidpoint hp hp1 ψ n)
    (hf : AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ)
      (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)))
    (hzero : sourcePsiContour hp hp1 n (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8) = 0)
    (M : ℝ) (hM : 0 ≤ M) (hsmall : M ≤ 1/2)
    (herror : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ M) :
    ‖displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
      (384/Real.pi)*M*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let f := sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ
  have hseg := sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have hτ := ball_subset_closedBall (hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
  have hlower : 1/2 ≤ ‖f τ‖ := by
    have htri : ‖I‖ ≤ ‖f τ-I‖+‖f τ‖ := by
      calc
        ‖I‖ = ‖(I-f τ)+f τ‖ := by congr 1; ring
        _ ≤ ‖I-f τ‖+‖f τ‖ := norm_add_le _ _
        _ = ‖f τ-I‖+‖f τ‖ := by rw [norm_sub_rev]
    rw [norm_I] at htri
    linarith [herror τ hτ]
  have h := norm_sourcePsi_midpointFilled_tail_offset_le hp hp1 n m hmn a ψ
    hmid hgap hroot hcircle havoid hf hzero M (1/2) hM (by norm_num) herror hlower
  convert h using 1
  field_simp
  ring

/-- Pointwise squared-gap estimates assemble into the actual lp
offset sequence, with zero at the omitted index and exact root
factorization also at collapsed retained gaps. -/
theorem exists_sourcePsi_squared_gap_offsets_of_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (B : Coeff p) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ m, m ≠ n →
      ‖displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
        C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*‖B m‖) :
    ∃ α : Coeff p, α n = 0 ∧
      (∀ m, m ≠ n → displacedRoots (a : Coeff p) m = sourceStandardRootMidpoint hp hp1 ψ m +
        (sourcePeriodicGapDisplacement hp hp1 ψ m)^2*α m) ∧ ‖α‖ ≤ C*‖B‖ := by
  let δ : ℤ → ℂ := fun m => if m = n then 0 else
    displacedRoots (a : Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m
  have hδ m : ‖δ m‖ ≤ C*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2*‖B m‖ := by
    by_cases hm : m = n
    · simp only [δ,if_pos hm,norm_zero]
      positivity
    · simpa only [δ,if_neg hm] using hbound m hm
  obtain ⟨α,hquot,hfactor,hnorm⟩ := exists_coeff_squared_weight_quotient
    (fun m => sourcePeriodicGapDisplacement hp hp1 ψ m) δ B C hC hδ
  refine ⟨α,?_,?_,hnorm⟩
  · rw [hquot n]
    simp only [δ,if_pos rfl,zero_div]
  · intro m hm
    have h := hfactor m
    simp only [δ,if_neg hm] at h
    linear_combination h

end NLS.ZakharovShabat
