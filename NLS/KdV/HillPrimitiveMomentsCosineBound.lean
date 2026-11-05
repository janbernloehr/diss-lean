import NLS.KdV.HillPrimitiveMomentsClosedGap
import NLS.ZakharovShabat.SourceGapCosineError

/-! Exact cosine averages and normalized gap bounds for the actual
rough Hill moments. Both formulas include complex and collapsed gaps. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch
variable {W : Set (CoeffPair 2)}

theorem centeredMoment_eq_cosine_average (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C) :
    P.centeredMoment W n m d q = (-(2*(Real.pi:ℂ))*I)*
      ∫ t in (0:ℝ)..1,
        let z := sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)+
          sourceStandardRootHalfGap (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)*
            (Real.cos ((2*Real.pi)*t):ℂ)
        (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^d*
          P.abelianGapNumerator n m (z,q) := by
  let ψ := P.sourcePsi q
  let D := P.isolating.periodCircle ψ (P.image q hq.1).2 (m:ℤ)
    (P.centers (m:ℤ)) (P.radii (m:ℤ)) (P.radii_pos _) (P.discs_eq _)
  let A : ℂ → ℂ := fun z => (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,ψ))^d*
    P.abelianGapNumerator n m (z,q)
  have hA : AnalyticOnNhd ℂ A (closedBall (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ))) := by
    intro z hz
    have hs := C.fullSquare_analytic (m:ℤ) ψ hq.2 z
      (fun j hj _ => D.closedBall_subset_omittedDomain hz j hj)
    exact (hs.pow d).mul
      ((P.analytic_abelianGapNumerator_on_patch n m (z,q) ⟨hz,hq.1⟩).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const))
  rw [P.centeredMoment_eq_square_contour C n m d q hq]
  have he : (∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
      (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,ψ))^d*
        P.abelianFrequencyDifferential n (z,q))=
      ∮ z in C((P.centers (m:ℤ):ℂ),P.radii (m:ℤ)),
        A z/sourceStandardRoot (by simp) (by norm_num) ψ (m:ℤ) z := by
    apply circleIntegral.integral_congr (P.radii_pos (m:ℤ)).le
    intro z hz
    dsimp only
    rw [P.abelianFrequencyDifferential_eq_gap_quotient n m (z,q) (D.sphere_subset_rootDomain hz)]
    dsimp only [A]
    rw [mul_div_assoc]
  rw [he]
  exact D.standardRoot_local_circle_period A hA

theorem norm_normalized_centeredMoment_le (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (d : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (B : ℝ) (hB : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ),
      ‖(sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^d*
        P.abelianGapNumerator n m (z,q)‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m d q‖ ≤ B := by
  rw [P.centeredMoment_eq_cosine_average C n m d q hq,← mul_assoc,norm_mul]
  have hn : ‖(2*Real.pi:ℂ)⁻¹ * (-(2*(Real.pi:ℂ))*I)‖=1 := by
    simp [mul_inv_rev,abs_of_pos Real.pi_pos]
    field_simp
  rw [hn,one_mul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := B)
    (f := fun t =>
      let z := sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)+
        sourceStandardRootHalfGap (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)*
          (Real.cos ((2*Real.pi)*t):ℂ)
      (sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q))^d*
        P.abelianGapNumerator n m (z,q)) (by
      intro t _
      apply hB
      rw [sourcePeriodicSegment_eq_midpoint_segment]
      simpa only [cosineGapPoint,← Complex.ofReal_cos] using
        cosineGapPoint_real_mem_segment
          (sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ))
          (sourceStandardRootHalfGap (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)) ((2*Real.pi)*t))
  simpa only [sub_zero,abs_one,mul_one] using hb

theorem norm_normalized_centeredSecondMoment_le (P : HillProductEquationPatch)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C)
    (S B : ℝ) (hS : 0 ≤ S)
    (hs : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ),
      ‖sourceFullAbelianSquare (by simp) (by norm_num) W (m:ℤ) (z,P.sourcePsi q)‖ ≤ S)
    (hb : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ),
      ‖P.abelianGapNumerator n m (z,q)‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 q‖ ≤ S*B := by
  apply P.norm_normalized_centeredMoment_le C n m 1 q hq (S*B)
  intro z hz
  simpa only [pow_one,norm_mul] using mul_le_mul (hs z hz) (hb z hz) (norm_nonneg _) hS

end NLS.KdV.HillProductEquationPatch
