import NLS.ZakharovShabat.SourceAbelianMomentAtlas
import NLS.ZakharovShabat.SourceAbelianMomentEvenNumerator
import NLS.ZakharovShabat.SourceStandardRootWeightedRealCircleBoundary

/-! # Real gap integrals for the normalized even moments

This supplies the contour-shrinking step of Lemma 20.3 for real sources.
The numerator is the canonical filled square times the regular psi factor.
No finite-gap assumption or extra contour choice is needed.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

/-- Every even normalized moment at an open real gap is minus twice
the upper-side integral of its canonical analytic numerator. -/
theorem real_even_moment_eq_gapSide
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    A.moment n k (2*m) φ.val =
      -(2 * gapSideBoundaryIntegral (sourceStandardRootMidpoint hp hp1 φ.val k)
        (sourceStandardRootHalfGap hp hp1 φ.val k)
        (sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n φ.val : Coeff p) φ.val) 1 true) := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  have hφ : φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨D⟩ := (A.localChart φ₀).charts φ.val hφ
  have hfamily := (A.localChart φ₀).family φ.val hφ
  let c := (A.localChart φ₀).center k
  let R := (A.localChart φ₀).contourRadius k
  have hc : (c.re : ℂ) = c := Complex.ext rfl (by simpa only [ofReal_im] using (hfamily.1 k).symm)
  have hg := (sourceAbelianMomentEvenNumerator_real_analytic hp hp1 W φ D n k m
    (s n φ.val : Coeff p)).mono (hfamily.2 k).2.2.1
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 k φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  calc
    A.moment n k (2*m) φ.val = sourceAbelianMomentCircle hp hp1 W n k (2*m)
        (s n φ.val : Coeff p) φ.val c R := A.moment_eq_local n k (2*m) φ₀ hφ
    _ = ∮ z in C(c,R), sourceAbelianMomentEvenNumerator hp hp1 W n k m
        (s n φ.val : Coeff p) φ.val z / sourceStandardRoot hp hp1 φ.val k z :=
      sourceAbelianMomentCircle_even_eq_weighted hp hp1 W n k m _ φ.val D c R
        (hfamily.2 k).1.le (hfamily.2 k).2.2.2
    _ = _ := by
      simpa only [hc] using weighted_sourceStandardRoot_realCenteredCircle_eq_boundary
        hp hp1 φ.val φ.property k hopen _ c.re R (hfamily.2 k).1
        (by simpa only [hc] using (hfamily.2 k).2.1)
        (by simpa only [hc] using hg)

/-- The second-moment gap-side identity includes collapsed gaps: both
sides vanish there, with no division by the gap length. -/
theorem real_second_moment_eq_gapSide
    (φ : realTypeSourceSubmodule p) (n k : ℤ) :
    A.moment n k 2 φ.val =
      -(2 * gapSideBoundaryIntegral (sourceStandardRootMidpoint hp hp1 φ.val k)
        (sourceStandardRootHalfGap hp hp1 φ.val k)
        (sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n φ.val : Coeff p) φ.val) 1 true) := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0
  · rw [A.moment_succ_of_collapsed φ.val (A.realType_subset_domain φ.property) n k hgap 1]
    have hδ : sourceStandardRootHalfGap hp hp1 φ.val k = 0 := by
      change canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k / 2 = 0
      rw [hgap,zero_div]
    rw [hδ]
    simp [gapSideBoundaryIntegral]
  · exact A.real_even_moment_eq_gapSide φ n k 1 hgap

/-- Cosine coordinates remove the endpoint singularities from each
open real gap integral, leaving an ordinary integral of the filled numerator. -/
theorem real_even_moment_eq_cosineIntegral
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    A.moment n k (2*m) φ.val = -(2*Complex.I) *
      ∫ θ in (0:ℝ)..Real.pi, sourceAbelianMomentEvenNumerator hp hp1 W n k m
        (s n φ.val : Coeff p) φ.val (sourceStandardRootMidpoint hp hp1 φ.val k +
          sourceStandardRootHalfGap hp hp1 φ.val k * (Real.cos θ:ℂ)) := by
  have hδ : sourceStandardRootHalfGap hp hp1 φ.val k ≠ 0 :=
    div_ne_zero hgap (by norm_num)
  rw [A.real_even_moment_eq_gapSide φ n k m hgap,
    gapSideBoundaryIntegral_eq_primitive _ _ _ _ hδ true]
  simp only [gapSidePrimitive,ite_true,Real.arccos_one]
  ring

/-- The contour estimate for every even order is attained on the gap
itself, rather than on an auxiliary isolating circle. -/
theorem real_even_moment_max_bound
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 φ.val k,
      (∀ w ∈ sourcePeriodicSegment hp hp1 φ.val k,
        ‖sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n φ.val : Coeff p) φ.val w‖ ≤
          ‖sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n φ.val : Coeff p) φ.val z‖) ∧
      ‖(2*Real.pi:ℂ)⁻¹ * A.moment n k (2*m) φ.val‖ ≤
        ‖sourceAbelianMomentEvenNumerator hp hp1 W n k m (s n φ.val : Coeff p) φ.val z‖ := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  have hφ : φ.val ∈ A.sourceBall φ₀ := mem_ball_self (A.localChart φ₀).radius_pos
  obtain ⟨D⟩ := (A.localChart φ₀).charts φ.val hφ
  have hfamily := (A.localChart φ₀).family φ.val hφ
  let c := (A.localChart φ₀).center k
  let R := (A.localChart φ₀).contourRadius k
  have hc : (c.re : ℂ) = c := Complex.ext rfl (by simpa only [ofReal_im] using (hfamily.1 k).symm)
  have hg := (sourceAbelianMomentEvenNumerator_real_analytic hp hp1 W φ D n k m
    (s n φ.val : Coeff p)).mono (hfamily.2 k).2.2.1
  have hopen := source_openRealGap_of_realType_gap_ne_zero hp hp1 k φ.val φ.property
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  have hb := weighted_sourceStandardRoot_realCenteredCircle_max_bound
    hp hp1 φ.val φ.property k hopen _ c.re R (hfamily.2 k).1
    (by simpa only [hc] using (hfamily.2 k).2.1) (by simpa only [hc] using hg)
  rw [hc] at hb
  rw [A.moment_eq_local n k (2*m) φ₀ hφ]
  change ∃ z ∈ sourcePeriodicSegment hp hp1 φ.val k, _ ∧
    ‖(2*Real.pi:ℂ)⁻¹ * sourceAbelianMomentCircle hp hp1 W n k (2*m)
      (s n φ.val : Coeff p) φ.val c R‖ ≤ _
  rw [sourceAbelianMomentCircle_even_eq_weighted hp hp1 W n k m _ φ.val D c R
    (hfamily.2 k).1.le (hfamily.2 k).2.2.2]
  exact hb

/-- A directly usable second-moment estimate, also valid at collapsed
gaps: separate bounds for the filled square and regular psi factor multiply. -/
theorem real_second_moment_norm_le
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hsquare : ∀ z ∈ sourcePeriodicSegment hp hp1 φ.val k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,φ.val)‖ ≤ M)
    (hregular : ∀ z ∈ sourcePeriodicSegment hp hp1 φ.val k,
      ‖sourceMomentRegularNumerator hp hp1 n k (s n φ.val : Coeff p) φ.val z‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹ * A.moment n k 2 φ.val‖ ≤ M*B := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0
  · rw [A.moment_succ_of_collapsed φ.val (A.realType_subset_domain φ.property) n k hgap 1]
    simpa only [mul_zero,norm_zero] using mul_nonneg hM hB
  · obtain ⟨z,hz,_,hb⟩ := A.real_even_moment_max_bound φ n k 1 hgap
    apply hb.trans
    simpa only [sourceAbelianMomentEvenNumerator,pow_one,norm_mul] using
      mul_le_mul (hsquare z hz) (hregular z hz) (norm_nonneg _) hM

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
