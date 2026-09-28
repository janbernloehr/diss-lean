import NLS.ZakharovShabat.SourcePsiDiagonalVariationNoAvoid
import NLS.ZakharovShabat.SourcePsiDeletedRootFill

/-!
# Diagonal psi variation with a freely filled omitted root

The scalar contour equation ignores the omitted root. Choosing its
location inside the omitted spectral disc makes the regular-factor
proof available without placing the artificial root `nπ` there.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal derivative formula for an arbitrary full root sequence. -/
theorem hasDerivAt_sourcePsiEquationCoordinate_diagonal_no_avoid
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : Coeff p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R, z ≠ displacedRoots a n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall c R)) :
    HasDerivAt
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (a + lp.single p m t) ψ c R)
      (∮ z in C(c,R),
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m a ψ z) /
            sourceStandardRoot hp hp1 ψ m z) 0 := by
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m a ψ z)
  let H : ℂ → ℂ := fun z => F z / sourceStandardRoot hp hp1 ψ m z
  let G : ℂ → ℂ := fun z => (displacedRoots a m-z)*H z
  have hHcont : ContinuousOn H (sphere c R) := by
    intro z hz
    have hzDomain : z ∉ sourcePeriodicSegment hp hp1 ψ m :=
      (hcircle hz) m
    exact ((hreg z (sphere_subset_closedBall hz)).div
      (sourceStandardRoot_analyticAt hp hp1 ψ m z hzDomain)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z hzDomain))
        |>.continuousAt.continuousWithinAt
  have hGcont : ContinuousOn G (sphere c R) := by
    exact (continuousOn_const.sub continuousOn_id).mul hHcont
  have hHint : CircleIntegrable H c R :=
    hHcont.circleIntegrable hR
  have hGint : CircleIntegrable G c R :=
    hGcont.circleIntegrable hR
  have hbase : sourcePsiEquationCoordinate hp hp1 n m
      a ψ c R = ∮ z in C(c,R), G z := by
    rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m a ψ c R hR hcircle havoidn]
    rw [←circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp [G,H,F]
    ring
  have hroot (t : ℂ) : displacedRoots (a+lp.single p m t) m =
      displacedRoots a m+t := by
    change (Real.pi : ℂ)*m + (a+lp.single p m t : Coeff p) m =
      ((Real.pi : ℂ)*m+a m)+t
    simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply_self]
    ring
  have hn (t : ℂ) : displacedRoots (a+lp.single p m t) n =
      displacedRoots a n := by
    change (Real.pi : ℂ)*n + (a+lp.single p m t : Coeff p) n =
      (Real.pi : ℂ)*n+a n
    simp only [lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ (Ne.symm hmn),add_zero]
  have hvariation (t : ℂ) :
      sourcePsiEquationCoordinate hp hp1 n m
        (a+lp.single p m t) ψ c R =
      sourcePsiEquationCoordinate hp hp1 n m a ψ c R +
        t*(∮ z in C(c,R), H z) := by
    have havoid' : ∀ z ∈ sphere c R,
        z ≠ displacedRoots (a+lp.single p m t) n := by
      intro z hz
      rw [hn]
      exact havoidn z hz
    have hfac := sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m (a+lp.single p m t) ψ c R hR hcircle havoid'
    conv_lhs => rw [hfac]
    rw [←circleIntegral.integral_const_mul]
    have hpoint : ∀ z ∈ sphere c R,
        (((n-m : ℤ) : ℂ) *
          (((displacedRoots (a+lp.single p m t) m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
            sourcePsiGapRegularFactor hp hp1 n m
              (a+lp.single p m t) ψ z)) =
          G z+t*H z := by
      intro z hz
      rw [sourcePsiGapRegularFactor_add_single_selected
        hp hp1 n m (Ne.symm hmn) a ψ z t,hroot]
      dsimp [G,H,F]
      ring
    rw [circleIntegral.integral_congr hR hpoint]
    have htHint : CircleIntegrable (fun z => t*H z) c R := by
      exact (continuousOn_const.mul hHcont).circleIntegrable hR
    rw [circleIntegral.integral_add hGint htHint,
      circleIntegral.integral_const_mul,←hbase]
  have heq : (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      (a+lp.single p m t) ψ c R) =
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        a ψ c R+t*(∮ z in C(c,R), H z)) := by
    funext t
    exact hvariation t
  rw [heq]
  change HasDerivAt
    (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
      a ψ c R+t*(∮ z in C(c,R), H z))
    (∮ z in C(c,R), H z) 0
  simpa using (((hasDerivAt_id (0 : ℂ)).mul_const
    (∮ z in C(c,R), H z)).const_add
      (sourcePsiEquationCoordinate hp hp1 n m a ψ c R))

/-- The same derivative formula for a deleted parameter, using any
chosen location for the omitted root. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_diagonal_filled
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ξ : ℂ) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (sourcePsiFillDeletedRoot n a ξ) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m
          (sourcePsiFillDeletedRoot n a ξ) ψ z))
      (closedBall c R)) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ c R)
      (∮ z in C(c,R),
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m
            (sourcePsiFillDeletedRoot n a ξ) ψ z) /
            sourceStandardRoot hp hp1 ψ m z) 0 := by
  have heq : (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      (a+Coeff.deletedSingleCLM n m hmn t) ψ c R) =
      (fun t : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (sourcePsiFillDeletedRoot n a ξ+lp.single p m t) ψ c R) := by
    funext t
    exact (sourcePsiEquationCoordinate_fillDeletedRoot_selectedLine
      hp hp1 n m hmn a ξ t ψ c R hR).symm
  rw [heq]
  exact hasDerivAt_sourcePsiEquationCoordinate_diagonal_no_avoid
    hp hp1 n m hmn (sourcePsiFillDeletedRoot n a ξ) ψ c R
      hR hcircle havoidn hreg

end NLS.ZakharovShabat
