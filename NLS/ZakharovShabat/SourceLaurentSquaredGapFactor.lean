import NLS.ComplexAnalysis.ParametricCircleIntegralHigher
import NLS.ZakharovShabat.SourceDiagonalLaurentCosine

/-! # Laurent actions divided analytically by the squared gap

Rationalizing the normalized spectral root removes its zero-gap baseline.
The baseline contour vanishes for every holomorphic spectral weight. The
remaining contour is analytic without inverting the action or gap, and a
Cauchy residue computes its value at a collapsed gap.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem normalizedStandardRoot_rationalizing_denom_ne_zero (τ q z : ℂ) (hτ : τ ≠ z) :
    τ-z+normalizedStandardRoot τ q z ≠ 0 := by
  have hd : τ-z ≠ 0 := sub_ne_zero.mpr hτ
  have hs : 1+Complex.sqrt (1-q/(4*(τ-z)^2)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hre
    have hpos : 0 ≤ (Complex.sqrt (1-q/(4*(τ-z)^2))).re := by
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      exact Real.sqrt_nonneg _
    linarith
  have he : τ-z+normalizedStandardRoot τ q z =
      (τ-z)*(1+Complex.sqrt (1-q/(4*(τ-z)^2))) := by
    unfold normalizedStandardRoot
    ring
  rw [he]
  exact mul_ne_zero hd hs

theorem normalizedStandardRoot_sub_zeroGap_factor (τ q z : ℂ) (hτ : τ ≠ z) :
    normalizedStandardRoot τ q z-(τ-z) = -q/(4*(τ-z+normalizedStandardRoot τ q z)) := by
  have hden := normalizedStandardRoot_rationalizing_denom_ne_zero τ q z hτ
  apply (eq_div_iff (mul_ne_zero (by norm_num) hden)).mpr
  have hsq := normalizedStandardRoot_sq τ q z hτ
  linear_combination 4*hsq

theorem normalizedPrimitiveCircle_squaredGap_factor
    (τ q c : ℂ) (R : ℝ) (hR : 0 < R) (hτ : τ ∈ ball c R)
    (w H : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall c R))
    (hH : AnalyticOnNhd ℂ H (closedBall c R))
    (hroot : ContinuousOn (normalizedStandardRoot τ q) (sphere c R)) :
    -(Real.pi : ℂ)⁻¹*(∮ z in C(c,R), w z*normalizedStandardRoot τ q z*H z) =
      q*((Real.pi : ℂ)⁻¹/4*(∮ z in C(c,R), w z*H z/(τ-z+normalizedStandardRoot τ q z))) := by
  have hτz (z : ℂ) (hz : z ∈ sphere c R) : τ ≠ z := by
    intro he
    exact sphere_disjoint_ball.le_bot ⟨hz,he ▸ hτ⟩
  have hden (z : ℂ) (hz : z ∈ sphere c R) : τ-z+normalizedStandardRoot τ q z ≠ 0 :=
    normalizedStandardRoot_rationalizing_denom_ne_zero τ q z (hτz z hz)
  have hB : AnalyticOnNhd ℂ (fun z => w z*(τ-z)*H z) (closedBall c R) :=
    fun z hz => ((hw z hz).mul (analyticAt_const.sub analyticAt_id)).mul (hH z hz)
  have hzero := (hB.differentiableOn.diffContOnCl_ball subset_rfl).circleIntegral_eq_zero hR.le
  have hBc : CircleIntegrable (fun z => w z*(τ-z)*H z) c R :=
    (hB.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hC : CircleIntegrable (fun z => w z*H z/(τ-z+normalizedStandardRoot τ q z)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((hw.continuousOn.mono sphere_subset_closedBall).mul
      (hH.continuousOn.mono sphere_subset_closedBall)).div
        ((continuous_const.sub continuous_id).continuousOn.add hroot) hden
  have hqC : CircleIntegrable (fun z => (q/4)*(w z*H z/(τ-z+normalizedStandardRoot τ q z))) c R :=
    hC.const_mul (q/4)
  have hInt : (∮ z in C(c,R), w z*normalizedStandardRoot τ q z*H z) =
      (∮ z in C(c,R), w z*(τ-z)*H z) -
        (q/4)*(∮ z in C(c,R), w z*H z/(τ-z+normalizedStandardRoot τ q z)) := by
    calc
      _ = ∮ z in C(c,R), w z*(τ-z)*H z -
          (q/4)*(w z*H z/(τ-z+normalizedStandardRoot τ q z)) := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        have he := normalizedStandardRoot_sub_zeroGap_factor τ q z (hτz z hz)
        calc
          _ = w z*((τ-z)+(normalizedStandardRoot τ q z-(τ-z)))*H z := by ring
          _ = _ := by rw [he]; field_simp [hden z hz]; ring
      _ = _ := by rw [circleIntegral.integral_sub hBc hqC,circleIntegral.integral_const_mul]
  rw [hInt,hzero]
  ring

theorem normalizedPrimitiveCircle_squaredGapFactor_zeroGap
    (τ c : ℂ) (R : ℝ) (hR : 0 < R) (hτ : τ ∈ ball c R)
    (w H : ℂ → ℂ) (hw : AnalyticOnNhd ℂ w (closedBall c R))
    (hH : AnalyticOnNhd ℂ H (closedBall c R)) :
    (Real.pi : ℂ)⁻¹/4*(∮ z in C(c,R), w z*H z/(τ-z+normalizedStandardRoot τ 0 z)) =
      -I/4*(w τ*H τ) := by
  have hE : AnalyticOnNhd ℂ (fun z => w z*H z) (closedBall c R) :=
    fun z hz => (hw z hz).mul (hH z hz)
  have hCauchy : (∮ z in C(c,R), (z-τ)⁻¹*(w z*H z)) = 2*(Real.pi : ℂ)*I*(w τ*H τ) := by
    simpa only [smul_eq_mul] using hE.differentiableOn.circleIntegral_sub_inv_smul hτ
  have he : (∮ z in C(c,R), w z*H z/(τ-z+normalizedStandardRoot τ 0 z)) =
      -(1/2 : ℂ)*(∮ z in C(c,R), (z-τ)⁻¹*(w z*H z)) := by
    calc
      _ = ∮ z in C(c,R), -(1/2 : ℂ)*((z-τ)⁻¹*(w z*H z)) := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        have hne : τ ≠ z := by
          intro he
          exact sphere_disjoint_ball.le_bot ⟨hz,he ▸ hτ⟩
        dsimp only
        rw [normalizedStandardRoot_zeroGap]
        field_simp
        ring
      _ = _ := by rw [circleIntegral.integral_const_mul]
  rw [he,hCauchy]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

namespace SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

def laurentSquaredGapCircle (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (n k : ℤ) (R : ℝ) (ψ : CoeffPair p) : ℂ :=
  (Real.pi : ℂ)⁻¹/4 * ∮ z in C(C.discs.center n,R),
    z^(k-1)*sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)/
      (sourceStandardRootMidpoint hp hp1 ψ n-z+sourceStandardRoot hp hp1 ψ n z)

theorem laurentPrimitiveCircle_eq_squaredGap_mul
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R) :
    sourceLaurentPrimitiveCircle hp hp1 W n k ψ (C.discs.center n) R =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
        C.laurentSquaredGapCircle n k R ψ := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let q := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2
  let H : ℂ → ℂ := fun z => sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)
  have hτ : τ ∈ ball (C.discs.center n) R :=
    ball_subset_ball hinner (C.discs.segment_subset ψ hψ n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
  have hw : AnalyticOnNhd ℂ (fun z : ℂ => z^(k-1)) (closedBall (C.discs.center n) R) := by
    intro z hz
    exact analyticAt_id.zpow (by intro he; exact hzero (he ▸ hz))
  have hH : AnalyticOnNhd ℂ H (closedBall (C.discs.center n) R) :=
    fun z hz => C.quotient_slice_analytic n ψ hψ z (closedBall_subset_ball houter hz)
  have hroot : ContinuousOn (normalizedStandardRoot τ q) (sphere (C.discs.center n) R) := by
    apply continuousOn_of_forall_continuousAt
    intro z hz
    exact (sourceStandardRoot_analyticAt hp hp1 ψ n z
      (C.intermediate_circle_root n ψ hψ R hinner houter z hz n)).continuousAt
  have hmain := normalizedPrimitiveCircle_squaredGap_factor τ q (C.discs.center n) R hR hτ
    (fun z => z^(k-1)) H hw hH hroot
  have he : (∮ z in C(C.discs.center n,R), z^(k-1)*sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) =
      ∮ z in C(C.discs.center n,R), z^(k-1)*normalizedStandardRoot τ q z*H z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    dsimp only
    rw [C.fullPrimitive_eq_cauchy n n ψ hψ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
        C.intermediate_circle_root n ψ hψ R hinner houter z hz n⟩]
    simp only [sub_self,mul_zero,add_zero,sourceFullAbelianCauchyPrimitive]
    change z^(k-1)*(normalizedStandardRoot τ q z*H z) = z^(k-1)*normalizedStandardRoot τ q z*H z
    ring
  change -(Real.pi : ℂ)⁻¹*(∮ z in C(C.discs.center n,R), z^(k-1)*sourceFullAbelianPrimitive hp hp1 W n (z,ψ)) = _
  rw [he]
  exact hmain

theorem laurentSquaredGapCircle_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ) (R : ℝ)
    (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUC : U ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (hrootOpen : IsOpen (sourceCanonicalRootJointDomain hp hp1 U))
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ n) U)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) U) :
    AnalyticOnNhd ℂ (C.laurentSquaredGapCircle n k R) U := by
  let D := (sourceCanonicalRootJointDomain hp hp1 U ∩ (ball (C.discs.center n) (C.discs.outer n) ×ˢ U)) ∩
    {t : ℂ × CoeffPair p | t.1 ≠ 0}
  have hD : IsOpen D := (hrootOpen.inter (isOpen_ball.prod hU)).inter (isOpen_ne_fun continuous_fst continuous_const)
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    t.1^(k-1)*sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) t/
      (sourceStandardRootMidpoint hp hp1 t.2 n-t.1+sourceStandardRoot hp hp1 t.2 n t.1)
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    rcases ht with ⟨⟨hr,ho⟩,hne⟩
    have hmid := (hτ t.2 hr.1).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
    have hrt := sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 t.2 n t.1
      (hτ t.2 hr.1) (hγ t.2 hr.1) (hr.2 n)
    have hQ := C.quotient_analytic n t ⟨ho.1,hUC hr.1⟩
    have hmidne : sourceStandardRootMidpoint hp hp1 t.2 n ≠ t.1 := by
      intro he
      exact hr.2 n (he ▸ sourcePeriodicMidpoint_mem_segment hp hp1 t.2 n)
    have hden := normalizedStandardRoot_rationalizing_denom_ne_zero
      (sourceStandardRootMidpoint hp hp1 t.2 n)
      ((canonicalPeriodicGap hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n)^2) t.1 hmidne
    exact ((analyticAt_fst.zpow hne).mul hQ).div ((hmid.sub analyticAt_fst).add hrt) hden
  have hcircle (ψ : CoeffPair p) (hψ : ψ ∈ U) (z : ℂ) (hz : z ∈ sphere (C.discs.center n) R) : (z,ψ) ∈ D := by
    refine ⟨⟨⟨hψ,C.intermediate_circle_root n ψ (hUC hψ) R hinner houter z hz⟩,
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),hψ⟩⟩,?_⟩
    intro he
    exact hzero (he ▸ sphere_subset_closedBall hz)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF (C.discs.center n) R
    ((C.discs.inner_pos n).trans_le hinner).le hU hcircle
  exact fun ψ hψ => analyticAt_const.mul (hi ψ hψ)


/-- Exact value of the regular Laurent factor when the selected gap is closed. -/
theorem laurentSquaredGapCircle_zeroGap
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n k : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    C.laurentSquaredGapCircle n k R ψ =
      -I/4*(sourceStandardRootMidpoint hp hp1 ψ n)^(k-1)*
        sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n)
          (sourceStandardRootMidpoint hp hp1 ψ n,ψ) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hτ : sourceStandardRootMidpoint hp hp1 ψ n ∈ ball (C.discs.center n) R :=
    ball_subset_ball hinner (C.discs.segment_subset ψ hψ n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))
  have hw : AnalyticOnNhd ℂ (fun z : ℂ => z^(k-1)) (closedBall (C.discs.center n) R) := by
    intro z hz
    exact analyticAt_id.zpow (by intro he; exact hzero (he ▸ hz))
  have hH : AnalyticOnNhd ℂ
      (fun z => sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ))
      (closedBall (C.discs.center n) R) :=
    fun z hz => C.quotient_slice_analytic n ψ hψ z (closedBall_subset_ball houter hz)
  have he := normalizedPrimitiveCircle_squaredGapFactor_zeroGap
    (sourceStandardRootMidpoint hp hp1 ψ n) (C.discs.center n) R hR hτ
    (fun z => z^(k-1))
    (fun z => sourceFullAbelianCauchyQuotient hp hp1 W n (C.discs.center n) (C.discs.outer n) (z,ψ)) hw hH
  unfold laurentSquaredGapCircle
  simp only [sourceStandardRoot,hgap,zero_pow (by norm_num : 2 ≠ 0)]
  rw [he]
  ring

/-- At a collapsed gap the inverse-frequency factor is the ordinary action
factor divided by the midpoint, with the same spectral normalization. -/
theorem laurentSquaredGapCircle_zero_eq_midpoint_inv_mul_one_of_zeroGap
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (hzero : (0 : ℂ) ∉ closedBall (C.discs.center n) R)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    C.laurentSquaredGapCircle n 0 R ψ =
      (sourceStandardRootMidpoint hp hp1 ψ n)⁻¹ * C.laurentSquaredGapCircle n 1 R ψ := by
  rw [C.laurentSquaredGapCircle_zeroGap n 0 ψ hψ R hinner houter hzero hgap,
    C.laurentSquaredGapCircle_zeroGap n 1 ψ hψ R hinner houter hzero hgap]
  norm_num
  ring

end SourceFullAbelianUniformCauchyFamily

end NLS.ZakharovShabat
