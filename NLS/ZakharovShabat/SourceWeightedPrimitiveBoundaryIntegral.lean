import NLS.ZakharovShabat.SourceHigherActionCircle
import NLS.ZakharovShabat.SourceRealHigherAction

/-! Analytic spectral weights in the actual primitive contour-to-gap formula.
The original operator, branch and exact action normalization are retained. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Collapse the spectrally weighted primitive contour onto its actual upper gap boundary. -/
theorem weighted_primitive_circle_eq_boundaryIntegral
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (n : ℤ)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (R : ℝ) (hinner : C.discs.inner n ≤ R) (houter : R < C.discs.outer n)
    (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q (closedBall (C.discs.center n) R)) :
    -(Real.pi:ℂ)⁻¹*(∮ z in C(C.discs.center n,R), q z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      (2/Real.pi : ℂ) * ∫ θ in (0 : ℝ)..Real.pi,
        q (sourceStandardRootMidpoint hp hp1 φ.val n+sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true) := by
  have hR : 0 < R := (C.discs.inner_pos n).trans_le hinner
  have hc : ((C.discs.center n).re : ℂ) = C.discs.center n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (C.discs.center_real n).symm)
  let g : ℂ → ℂ := fun z => q z * C.powerNumerator n 0 φ.val z
  have hg : AnalyticOnNhd ℂ g (closedBall (C.discs.center n) R) :=
    fun z hz => (hq z hz).mul
      (C.powerNumerator_analytic n 0 φ.val hφ z (closedBall_subset_ball houter hz))
  have hseg := (C.discs.segment_subset φ.val hφ n).trans (ball_subset_ball hinner)
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 n φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have he := weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 φ.val φ.property n hopen
    g (C.discs.center n).re R hR (by simpa only [hc] using hseg) (by simpa only [hc] using hg)
  rw [hc,gapSideBoundaryIntegral_eq_primitive _ _ _ _ (div_ne_zero hgap (by norm_num)) true] at he
  simp only [gapSidePrimitive,ite_true,Real.arccos_one] at he
  obtain ⟨E⟩ := C.charts φ.val hφ
  have hw : (∮ z in C(C.discs.center n,R), q z*sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)) =
      ∮ z in C(C.discs.center n,R), g z / sourceStandardRoot hp hp1 φ.val n z := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz' := C.primitive_odd_eq_weighted n 0 φ.val hφ z
      ⟨closedBall_subset_ball houter (sphere_subset_closedBall hz),
        C.intermediate_circle_root n φ.val hφ R hinner houter z hz n⟩
    simp only [Nat.mul_zero,zero_add,pow_one] at hz'
    dsimp only
    rw [hz']
    exact (mul_div_assoc _ _ _).symm
  rw [hw,he]
  have hpoint (θ : ℝ) : g (sourceStandardRootMidpoint hp hp1 φ.val n+
      sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) =
      -I * (q (sourceStandardRootMidpoint hp hp1 φ.val n+
        sourceStandardRootHalfGap hp hp1 φ.val n*(Real.cos θ:ℂ)) *
        ((sourceStandardRootHalfGap hp hp1 φ.val n*(Real.sin θ:ℂ))*C.gapBoundary n φ.val θ true)) := by
    dsimp only [g]
    rw [C.powerNumerator_cosine]
    simp only [Nat.mul_zero,zero_add,pow_one]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  simp only [I_sq]
  ring


end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
