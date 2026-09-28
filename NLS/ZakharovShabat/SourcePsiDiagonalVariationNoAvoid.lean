import NLS.ZakharovShabat.SourcePsiDiagonalRootCancellation

/-!
# Diagonal psi variation with no selected-root contour avoidance

The selected-root factor is linear in that root, while the quotient
with this index omitted is independent of it. Differentiating the
gap-factorized contour equation therefore removes the selected-root
factor directly, including when the selected root lies on the
contour. Only the deleted equation root must avoid the contour.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal scalar derivative is the regular-factor contour
integral without requiring the selected retained root to avoid the
contour. -/
theorem hasDerivAt_sourcePsiDeletedEquationCoordinate_diagonal_no_avoid
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (havoidn : ∀ z ∈ sphere c R,
      z ≠ displacedRoots (a : Coeff p) n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c R)) :
    HasDerivAt
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ c R)
      (∮ z in C(c,R),
        (((n-m : ℤ) : ℂ) *
          sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z) /
            sourceStandardRoot hp hp1 ψ m z) 0 := by
  let F : ℂ → ℂ := fun z => (((n-m : ℤ) : ℂ) *
    sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  let H : ℂ → ℂ := fun z => F z / sourceStandardRoot hp hp1 ψ m z
  let G : ℂ → ℂ := fun z => (displacedRoots (a : Coeff p) m-z)*H z
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
  have hbase : sourcePsiDeletedEquationCoordinate hp hp1 n m
      a ψ c R = ∮ z in C(c,R), G z := by
    change sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ c R = _
    rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m (a : Coeff p) ψ c R hR hcircle havoidn]
    rw [←circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR
    intro z hz
    dsimp [G,H,F]
    ring
  have hroot (t : ℂ) : displacedRoots
      ((a : Coeff p)+lp.single p m t) m =
        displacedRoots (a : Coeff p) m+t := by
    change (Real.pi : ℂ)*m +
      ((a : Coeff p)+lp.single p m t : Coeff p) m =
        ((Real.pi : ℂ)*m+(a : Coeff p) m)+t
    simp only [lp.coeFn_add,Pi.add_apply,lp.single_apply_self]
    ring
  have hn (t : ℂ) : displacedRoots
      ((a : Coeff p)+lp.single p m t) n =
        displacedRoots (a : Coeff p) n := by
    change (Real.pi : ℂ)*n +
      ((a : Coeff p)+lp.single p m t : Coeff p) n =
        (Real.pi : ℂ)*n+(a : Coeff p) n
    simp only [lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ (Ne.symm hmn),add_zero]
  have hcoe (t : ℂ) :
      ((a+Coeff.deletedSingleCLM n m hmn t : DeletedCoeff p n) : Coeff p) =
        (a : Coeff p)+lp.single p m t := by
    rw [Submodule.coe_add,Coeff.deletedSingleCLM_coe]
  have hvariation (t : ℂ) :
      sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ c R =
      sourcePsiDeletedEquationCoordinate hp hp1 n m a ψ c R +
        t*(∮ z in C(c,R), H z) := by
    have havoid' : ∀ z ∈ sphere c R,
        z ≠ displacedRoots
          ((a : Coeff p)+lp.single p m t) n := by
      intro z hz
      rw [hn]
      exact havoidn z hz
    change sourcePsiEquationCoordinate hp hp1 n m
        ((a+Coeff.deletedSingleCLM n m hmn t : DeletedCoeff p n) : Coeff p)
          ψ c R = _
    rw [hcoe]
    have hfac := sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
      hp hp1 n m ((a : Coeff p)+lp.single p m t) ψ c R
        hR hcircle havoid'
    conv_lhs => rw [hfac]
    rw [←circleIntegral.integral_const_mul]
    have hpoint : ∀ z ∈ sphere c R,
        (((n-m : ℤ) : ℂ) *
          (((displacedRoots ((a : Coeff p)+lp.single p m t) m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
            sourcePsiGapRegularFactor hp hp1 n m
              ((a : Coeff p)+lp.single p m t) ψ z)) =
          G z+t*H z := by
      intro z hz
      rw [sourcePsiGapRegularFactor_add_single_selected
        hp hp1 n m (Ne.symm hmn) (a : Coeff p) ψ z t,hroot]
      dsimp [G,H,F]
      ring
    rw [circleIntegral.integral_congr hR hpoint]
    have htHint : CircleIntegrable (fun z => t*H z) c R := by
      exact (continuousOn_const.mul hHcont).circleIntegrable hR
    rw [circleIntegral.integral_add hGint htHint,
      circleIntegral.integral_const_mul,←hbase]
  have heq : (fun t : ℂ =>
      sourcePsiDeletedEquationCoordinate hp hp1 n m
        (a+Coeff.deletedSingleCLM n m hmn t) ψ c R) =
      (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
        a ψ c R+t*(∮ z in C(c,R), H z)) := by
    funext t
    exact hvariation t
  rw [heq]
  change HasDerivAt
    (fun t : ℂ => sourcePsiDeletedEquationCoordinate hp hp1 n m
      a ψ c R+t*(∮ z in C(c,R), H z))
    (∮ z in C(c,R), H z) 0
  simpa using (((hasDerivAt_id (0 : ℂ)).mul_const
    (∮ z in C(c,R), H z)).const_add
      (sourcePsiDeletedEquationCoordinate hp hp1 n m a ψ c R))

end NLS.ZakharovShabat
