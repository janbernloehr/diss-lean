import NLS.ZakharovShabat.SourcePsiRealTailOpenGap

/-!
# Reality of psi coordinates on real-centered open-gap contours

The selected contour need not be free-centered. When it is centered
on the real axis, encloses a real open gap, and the weighted regular
factor extends analytically through the enclosed disc, Lemma 12.3
makes the factorized psi equation coordinate real.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The psi equation coordinate of an open real gap is real on any
real-centered enclosing circle where its weighted regular factor is
analytic. -/
theorem sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_openRealGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n m : ℤ) (a : Coeff p)
    (hroots : ∀ k : ℤ, (displacedRoots a k).im = 0)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re)
    (x R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) R)
    (hdom : closedBall (x:ℂ) R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : sphere (x:ℂ) R ⊆
      sourceCanonicalRootDomain hp hp1 ψ)
    (havoid : ∀ z ∈ sphere (x:ℂ) R, z ≠ displacedRoots a n)
    (hreg : AnalyticOnNhd ℂ
      (fun z => (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z))
      (closedBall (x:ℂ) R)) :
    (sourcePsiEquationCoordinate hp hp1 n m a ψ (x:ℂ) R).im = 0 := by
  let c : ℂ := (x:ℂ)
  let g : ℂ → ℂ := fun z =>
    (-I) * (displacedRoots a m-z) *
      (((n-m : ℤ) : ℂ) *
        sourcePsiGapRegularFactor hp hp1 n m a ψ z)
  have hgap : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m) ⊆ ball c R :=
    (sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m).trans hseg
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := by
    intro z hz
    exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).mul
      (hreg z hz)
  have hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ m)
      (sourceStandardRootHalfGap hp hp1 ψ m), (g z).im = 0 := by
    intro z hz
    exact sourcePsiGapNumerator_rotated_im_eq_zero_on_selectedGap
      hp hp1 ψ hreal a hroots n m c R hseg hdom z hz
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_realCenteredCircle_real_mean_value
      hp hp1 ψ hreal m hopen g hgreal x R hR hseg hgap hg
  let J : ℂ := ∮ z in C(c,R),
    g z / sourceStandardRoot hp hp1 ψ m z
  have hEq : sourcePsiEquationCoordinate hp hp1 n m a ψ c R = I*J := by
    calc
      sourcePsiEquationCoordinate hp hp1 n m a ψ c R =
        ∮ z in C(c,R),
          ((displacedRoots a m-z) /
            sourceStandardRoot hp hp1 ψ m z) *
            (((n-m : ℤ) : ℂ) *
              sourcePsiGapRegularFactor hp hp1 n m a ψ z) := by
                rw [sourcePsiEquationCoordinate_eq_gap_factor_circleIntegral
                  hp hp1 n m a ψ c R hR.le hcircle havoid]
                rw [← circleIntegral.integral_const_mul]
                apply circleIntegral.integral_congr hR.le
                intro z _
                ring
      _ = I*J := by
        rw [← circleIntegral.integral_const_mul]
        apply circleIntegral.integral_congr hR.le
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
