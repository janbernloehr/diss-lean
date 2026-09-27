import NLS.ZakharovShabat.SourceStandardRootComplexGapCircleEstimate
import NLS.ZakharovShabat.SourcePsiNearFreeRegularAnalytic

/-!
# Psi contour coordinates for complex near-free gaps

The selected-root factorization and complex-gap contour estimate give
the psi coordinate bound without a real-type source assumption.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A complex near-free psi coordinate is controlled by its root-to-
midpoint displacement and a quadratic complex-gap correction. -/
theorem nearFree_complex_deletedPsi_normalizedCoordinate_bound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (hgeom : closedBall ((Real.pi : ℂ)*m) (Real.pi/4) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (B : Coeff p)
    (hB : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖(((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (a : Coeff p) ψ z)‖ ≤
        (2/Real.pi)*(1+‖B m‖)) :
    let σ := displacedRoots (a : Coeff p) m
    let τ := sourceStandardRootMidpoint hp hp1 ψ m
    let c : ℂ := (Real.pi : ℂ)*m
    let L : ℝ := (2/Real.pi)*(1+‖B m‖)
    ‖(2*(Real.pi:ℂ))⁻¹ *
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
        c (Real.pi/8)‖ ≤
      ‖τ-σ‖*L +
        (Real.pi/8)*(‖σ-c‖+Real.pi/8)*L*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
            (2*(Real.pi/16)^3)) := by
  let σ := displacedRoots (a : Coeff p) m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let c : ℂ := (Real.pi : ℂ)*m
  let L : ℝ := (2/Real.pi)*(1+‖B m‖)
  let f : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  dsimp only
  have hreg : AnalyticOnNhd ℂ f (closedBall c (Real.pi/4)) := by
    apply analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m (Ne.symm hmn) a ψ W hψW hQ
        (Real.pi/4) (by nlinarith [Real.pi_pos])
    exact hgeom
  have havoid : ∀ z ∈ sphere c (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  have hEq : sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      c (Real.pi/8) =
      ∮ z in C(c,Real.pi/8),
        ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z := by
    rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m (a : Coeff p) ψ c (Real.pi/8)
        (by positivity) hcircle havoid]
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr (by positivity)
    intro z _
    dsimp [σ,f]
    ring
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound : ‖(2*(Real.pi:ℂ))⁻¹ *
      (∮ z in C(c,Real.pi/8),
        ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z)‖ ≤
      ‖τ-σ‖*‖f τ‖ +
        (Real.pi/8)*(‖σ-c‖+Real.pi/8)*L*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
            (2*(Real.pi/16)^3)) :=
    norm_nearFree_complexGap_weighted_circle_le
      hp hp1 ψ m σ hmid hgap f hreg L hL hB
  rw [hEq]
  have hτdisc : τ ∈ closedBall c (Real.pi/8) := by
    rw [mem_closedBall,dist_eq_norm]
    exact hmid.trans (by nlinarith [Real.pi_pos])
  have hfactor : ‖f τ‖ ≤ L := hB τ hτdisc
  exact hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left hfactor (norm_nonneg _)) le_rfl)

end NLS.ZakharovShabat
