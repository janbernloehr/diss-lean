import NLS.ZakharovShabat.SourcePrimitivePowerBoundary
import NLS.ZakharovShabat.SourceFullAbelianRealBoundary

/-! # Real arcosh integral for the odd primitive-power moments -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The positive real gap profile in cosine coordinates. -/
def sourceRealGapCosineProfile (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (θ : ℝ) : ℝ :=
  sourceRealGapArcoshProfile hp φ n (realGapAffinePoint hp hp1 φ n (Real.cos θ))

theorem SourceFullAbelianUniformCauchyFamily.gapBoundary_eq_realCosineProfile
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) :
    C.gapBoundary n φ.val θ true = (sourceRealGapCosineProfile hp hp1 φ.val n θ : ℂ) := by
  let x := realGapAffinePoint hp hp1 φ.val n (Real.cos θ)
  have hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
    have hz := sourceCanonicalRootGapPoint_mem_segment hp hp1 φ.val n (Real.cos θ)
      (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    have h := sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val n _ hz
    rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n,ofReal_re] at h
    exact h
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hside := sourceCanonicalRootGapPoint_vertical_tendsto_upperSide hp hp1 φ.val φ.property n hopen (Real.cos θ)
  have hlim := (C.fullPrimitive_tendsto_gapBoundary n φ.val hφ hgap θ hθ true).comp hside
  rw [sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 φ.val φ.property n] at hlim
  have hv : Tendsto (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) (𝓝[Ioi 0] 0)
      (𝓝[sourceAbelianHalfPlane true] (x:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun y : ℝ => (x:ℂ)+(y:ℂ)*I) 0 := by fun_prop
      simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact sourceAbelian_vertical_mem_halfPlane true x y hy
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hr := (sourceFullAbelianPrimitive_real_gap_boundary_limit φ E n true x hx).comp hv
  exact tendsto_nhds_unique hlim hr

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- A real-source moment may be computed using any compatible Cauchy family. -/
theorem real_moment_eq_cauchyCircle (C : SourceFullAbelianUniformCauchyFamily hp hp1 V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n : ℤ) (m : ℕ) (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n) :
    A.moment n m φ.val = sourcePrimitivePowerCircle hp hp1 V n m φ.val (C.discs.center n) R := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  have hφ₀ : φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨D⟩ := (A.localChart φ₀).charts φ.val hφ₀
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hF := (A.localChart φ₀).family φ.val hφ₀
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  exact (A.moment_eq_local n m φ₀ hφ₀).trans
    ((sourcePrimitivePowerCircle_eq_of_realCentered_enclosingCircles hp hp1 W n m φ.val D φ.property
      _ _ _ _ (hF.1 n) (C.discs.center_real n) (hF.2 n).1 hR (hF.2 n).2.1
      ((C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)) (hF.2 n).2.2.1
      ((closedBall_subset_closedBall houter.le).trans (C.discs.avoids_other φ.val hφ n))).trans
      (sourcePrimitivePowerCircle_independent_neighborhood hp hp1 W V n m φ.val D E _ _ hR.le
        (C.intermediate_circle_root n φ.val hφ R hinner houter)))

/-- Odd moments are real gap integrals of positive arcosh powers.
The formula includes collapsed gaps without dividing by the gap length. -/
theorem real_odd_moment_eq_cosineIntegral (φ : realTypeSourceSubmodule p) (n : ℤ) (m : ℕ) :
    A.moment n (2*m+1) φ.val =
      (((canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re / Real.pi *
        ∫ θ in (0:ℝ)..Real.pi, Real.sin θ * (sourceRealGapCosineProfile hp hp1 φ.val n θ)^(2*m+1) : ℝ) : ℂ) := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0
  · rw [A.moment_of_collapsed φ.val (A.realType_subset_domain φ.property) n hgap (2*m+1),hgap]
    simp
  obtain ⟨V,_,_,hC⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hCφ⟩ := hC φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hCφ]
    exact mem_ball_self C.discs.sourceRadius_pos
  let R := (C.discs.inner n+C.discs.outer n)/2
  have hinner : C.discs.inner n ≤ R := by dsimp [R]; linarith [C.discs.inner_lt n]
  have houter : R < C.discs.outer n := by dsimp [R]; linarith [C.discs.inner_lt n]
  rw [A.real_moment_eq_cauchyCircle C φ hφ n (2*m+1) R hinner houter,
    C.powerCircle_odd_eq_boundaryIntegral n m φ hφ hgap R hinner houter]
  have he : (∫ θ in (0:ℝ)..Real.pi,
      (sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*(C.gapBoundary n φ.val θ true)^(2*m+1)) =
      sourceStandardRootHalfGap hp hp1 φ.val n *
        (∫ θ in (0:ℝ)..Real.pi, (Real.sin θ * (sourceRealGapCosineProfile hp hp1 φ.val n θ)^(2*m+1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    dsimp only
    rw [C.gapBoundary_eq_realCosineProfile n φ hφ hgap θ hθ]
    simp only [ofReal_mul,ofReal_pow,mul_assoc]
  rw [he,intervalIntegral.integral_ofReal,sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 φ.val φ.property n]
  simp only [ofReal_mul,ofReal_div,ofReal_sub,ofReal_ofNat,canonicalPeriodicGap,sub_re]
  ring

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
