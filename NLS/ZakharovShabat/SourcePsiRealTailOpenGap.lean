import NLS.ZakharovShabat.SourcePsiRealGapQuotient
import NLS.ZakharovShabat.SourcePsiSelectedGapContourBound
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue

/-!
# Reality of open-gap psi coordinates on free-centered tail circles

The rotated factorized numerator is real on a real periodic gap. For
small tail gaps, the free eighth-π contour lies inside a midpoint
circle in the quotient's analytic domain, so the real mean-value form
of Lemma 12.3 makes the psi equation coordinate real.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A real-type open gap with small free-centered geometry has a real
psi equation coordinate on its free eighth-π contour. -/
theorem sourcePsiEquationCoordinate_freeEighth_im_eq_zero_of_openRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (hnm : n ≠ m) (a : DeletedCoeff p n)
    (hroots : ∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (W : Set (CoeffPair p)) (hψW : ψ ∈ W)
    (hQ : AnalyticOnNhd ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (sourceSingleRootQuotientJointDomain hp hp1 W m))
    (hdom : closedBall ((Real.pi : ℂ)*m) (Real.pi/4) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32) :
    (sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      ((Real.pi : ℂ)*m) (Real.pi/8)).im = 0 := by
  let c : ℂ := (Real.pi : ℂ)*m
  let U : Set ℂ := ball c (Real.pi/4)
  let g : ℂ → ℂ := fun z =>
    (-I) * (displacedRoots (a : Coeff p) m-z) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z)
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c (Real.pi/8) :=
    sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ U := by
    exact (sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m).trans
        (hseg.trans (ball_subset_ball (by nlinarith [Real.pi_pos])))
  have hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
      (closedBall c (Real.pi/4)) :=
    analyticOnNhd_deletedPsi_gapRegularFactor_of_omitted_disc
      hp hp1 n m hnm a ψ W hψW hQ (Real.pi/4)
        (by nlinarith [Real.pi_pos]) hdom
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hz' : z ∈ closedBall c (Real.pi/4) := ball_subset_closedBall hz
    exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).mul
      (hreg z hz')
  have hdom8 : closedBall c (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall
      (by nlinarith [Real.pi_pos])).trans hdom
  have hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (g z).im = 0 := by
    intro z hz
    exact sourcePsiGapNumerator_rotated_im_eq_zero_on_selectedGap
      hp hp1 ψ hreal (a : Coeff p) hroots n m c (Real.pi/8)
        hseg hdom8 z hz
  obtain ⟨hR,hUdisc,hnest⟩ := nearFree_realGap_nested_circle_geometry
    hp hp1 ψ hreal m hopen hmid hgap
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_circle_real_mean_value_of_local_nested_midpoint
      hp hp1 ψ hreal m hopen g U isOpen_ball hgapU hg hgreal
        c (Real.pi/8) (3*Real.pi/16) (by positivity) hseg
        hR hUdisc hnest
  have havoid : ∀ z ∈ sphere c (Real.pi/8),
      z ≠ displacedRoots (a : Coeff p) n := by
    intro z hz
    have ha : (a : Coeff p) n = 0 := a.property
    rw [show displacedRoots (a : Coeff p) n =
      (Real.pi : ℂ)*n by simp [displacedRoots,ha]]
    exact freeCircle_point_ne_freeCenter m n (Real.pi/8)
      (by positivity) (by nlinarith [Real.pi_pos]) z hz
  let J : ℂ := ∮ z in C(c,Real.pi/8),
    g z / sourceStandardRoot hp hp1 ψ m z
  have hEq : sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
      c (Real.pi/8) = I*J := by
    calc
      sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          c (Real.pi/8) =
        ∮ z in C(c,Real.pi/8),
          ((displacedRoots (a : Coeff p) m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
            (((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z) := by
                rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
                  hp hp1 n m (a : Coeff p) ψ c (Real.pi/8)
                    (by positivity) hcircle havoid]
                rw [← circleIntegral.integral_const_mul]
                apply circleIntegral.integral_congr (by positivity)
                intro z _
                ring
      _ = I*J := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr (by positivity)
        intro z _
        dsimp [g]
        ring_nf
        simp [Complex.I_sq]
        ring
  let K : ℂ := 2*(Real.pi:ℂ)*I
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hJ : J = K*(-g μ) := by
    have hvalue' : K⁻¹*J = -g μ := hvalue
    calc
      J = K*(K⁻¹*J) := by
        rw [← mul_assoc,mul_inv_cancel₀ hK,one_mul]
      _ = K*(-g μ) := by rw [hvalue']
  have hrealμ : (g μ).im = 0 := hgreal μ hμ
  rw [hEq,hJ]
  have heq : I*(K*(-g μ)) = (2*(Real.pi:ℂ))*g μ := by
    dsimp [K]
    ring_nf
    simp [Complex.I_sq]
  rw [heq]
  simp [Complex.mul_im,hrealμ]

end NLS.ZakharovShabat
