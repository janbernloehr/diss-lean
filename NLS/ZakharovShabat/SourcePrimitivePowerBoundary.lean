import NLS.ZakharovShabat.SourcePrimitivePowerAction
import NLS.ZakharovShabat.SourceStandardRootWeightedRealCircleBoundary

/-! # Odd primitive powers as gap-side integrals

Multiplying an odd power by the selected root removes its cut. On a
real gap the weighted-circle formula then expresses the moment as an
ordinary cosine integral of the actual upper boundary power.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def powerNumerator (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (m : ℕ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (C.square n (z,ψ))^m * sourceAngularSelectedPolynomial hp hp1 ψ n z *
    sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)

theorem powerNumerator_analytic (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (m : ℕ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) :
    AnalyticOnNhd ℂ (C.powerNumerator n m ψ) (ball (C.discs.center n) (C.discs.outer n)) := by
  intro z hz
  have hpoly : AnalyticAt ℂ (sourceAngularSelectedPolynomial hp hp1 ψ n) z :=
    ((analyticAt_id.sub analyticAt_const).pow 2).sub analyticAt_const
  exact (((C.square_analytic n ψ hψ z hz).pow m).mul hpoly).mul
    (C.quotient_slice_analytic n ψ hψ z hz)

theorem primitive_odd_eq_weighted (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (m : ℕ) (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (z : ℂ) (hz : z ∈ ball (C.discs.center n) (C.discs.outer n) \ sourcePeriodicSegment hp hp1 ψ n) :
    (sourceFullAbelianPrimitive hp hp1 W n (z,ψ))^(2*m+1) =
      C.powerNumerator n m ψ z / sourceStandardRoot hp hp1 ψ n z := by
  have hr := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz.2
  have hs : sourceAngularSelectedPolynomial hp hp1 ψ n z = (sourceStandardRoot hp hp1 ψ n z)^2 := by
    rw [sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz.2,
      sourceAngularSelectedPolynomial_eq_endpoint_factor]
  rw [pow_succ,pow_mul,← C.square_eq_fullPrimitive_sq n ψ hψ z hz,
    C.fullPrimitive_eq_cauchy n n ψ hψ z hz]
  simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive,powerNumerator,hs]
  field_simp

/-- The filled odd numerator on the gap is the selected upper root
times the corresponding odd boundary power, including endpoints. -/
theorem powerNumerator_cosine (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n : ℤ) (m : ℕ) (ψ : CoeffPair p) (θ : ℝ) :
    C.powerNumerator n m ψ (sourceStandardRootMidpoint hp hp1 ψ n +
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)) =
      -I * (sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ)) *
        (C.gapBoundary n ψ θ true)^(2*m+1) := by
  have hpoly : sourceAngularSelectedPolynomial hp hp1 ψ n
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)) =
      -(sourceStandardRootHalfGap hp hp1 ψ n*(Real.sin θ:ℂ))^2 := by
    have htrig := Complex.sin_sq_add_cos_sq (θ:ℂ)
    simp only [← Complex.ofReal_sin,← Complex.ofReal_cos] at htrig
    unfold sourceAngularSelectedPolynomial quadraticRootPolynomial sourceStandardRootHalfGap
    linear_combination (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2/4*htrig
  rw [powerNumerator,C.square_eq_gapBoundary_sq n ψ θ true,← pow_mul]
  rw [pow_succ,hpoly]
  simp only [gapBoundary,ite_true]
  ring_nf
  simp only [I_sq]
  ring

/-- The exact odd-moment boundary formula on an intermediate real circle. -/
theorem powerCircle_odd_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ) (m : ℕ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    sourcePrimitivePowerCircle hp hp1 W n (2*m+1) φ.val (C.discs.center n) R =
      (2/Real.pi:ℂ) * ∫ θ in (0:ℝ)..Real.pi,
        (sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ)) *
          (C.gapBoundary n φ.val θ true)^(2*m+1) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hc : ((C.discs.center n).re:ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  have hg := (C.powerNumerator_analytic n m φ.val hφ).mono (closedBall_subset_ball houter)
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have he := weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 φ.val φ.property n hopen
    (C.powerNumerator n m φ.val) (C.discs.center n).re R hR
    (by simpa only [hc] using hseg) (by simpa only [hc] using hg)
  rw [hc,gapSideBoundaryIntegral_eq_primitive _ _ _ _ (div_ne_zero hgap (by norm_num)) true] at he
  simp only [gapSidePrimitive,ite_true,Real.arccos_one] at he
  have hweighted : (∮ z in C(C.discs.center n,R),
      (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))^(2*m+1)) =
      ∮ z in C(C.discs.center n,R), C.powerNumerator n m φ.val z / sourceStandardRoot hp hp1 φ.val n z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact C.primitive_odd_eq_weighted n m φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hz n⟩
  rw [sourcePrimitivePowerCircle,hweighted,he]
  simp only [C.powerNumerator_cosine,mul_assoc,intervalIntegral.integral_const_mul]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
