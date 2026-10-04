import NLS.ZakharovShabat.SourceGapCosineMeanAnalytic

/-! # Real cosine formulas including closed gaps

Positive even moments have the regular cosine representation even when
the selected endpoints coincide. The filled square vanishes at that
endpoint, so no division by the gap is needed.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

include A in
/-- The actual numerator vanishes at the midpoint of a collapsed real
gap for every positive even order. -/
theorem real_evenNumerator_midpoint_of_collapsed
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0) :
    sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n φ.val : Coeff p) φ.val
      (sourceStandardRootMidpoint hp hp1 φ.val k) = 0 := by
  let φ₀ : realTypeSourceLocus p := ⟨φ.val,φ.property⟩
  obtain ⟨D⟩ := (A.localChart φ₀).charts φ.val (mem_ball_self (A.localChart φ₀).radius_pos)
  have he := sub_eq_zero.mp hgap
  have hmid : sourceStandardRootMidpoint hp hp1 φ.val k =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k := by
    change (_ + _) / 2 = _
    rw [he]
    ring
  unfold sourceAbelianMomentEvenNumerator
  rw [hmid,sourceFullAbelianSquare_eq_real φ D k,
    (sourceAbelianSquare_endpoints hp hp1 φ.val φ.property k).1]
  simp

/-- The regular cosine formula holds at all real sources for every
positive even moment, including collapsed selected gaps. -/
theorem real_positive_even_moment_eq_cosineMean
    (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ) :
    A.moment n k (2*(m+1)) φ.val = -(2*Complex.I) *
      sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
        sourceAbelianMomentEvenNumerator hp hp1 W n k (m+1) (s n t.2 : Coeff p) t.2 t.1) φ.val := by
  by_cases hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k = 0
  · have hm : 2*(m+1) = (2*m+1)+1 := by omega
    rw [hm,A.moment_succ_of_collapsed φ.val (A.realType_subset_domain φ.property) n k hgap (2*m+1)]
    have hδ : sourceStandardRootHalfGap hp hp1 φ.val k = 0 := by
      change canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k / 2 = 0
      rw [hgap,zero_div]
    simp only [sourceGapCosineMean,parametricCosineMean,hδ,zero_mul,add_zero,
      A.real_evenNumerator_midpoint_of_collapsed φ n k m hgap,intervalIntegral.integral_zero,mul_zero]
  · exact A.real_even_moment_eq_cosineIntegral φ n k (m+1) hgap

/-- The second-moment version used in Lemma 20.3 has no open-gap premise. -/
theorem real_second_moment_eq_cosineMean
    (φ : realTypeSourceSubmodule p) (n k : ℤ) :
    A.moment n k 2 φ.val = -(2*Complex.I) *
      sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
        sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n t.2 : Coeff p) t.2 t.1) φ.val :=
  A.real_positive_even_moment_eq_cosineMean φ n k 0

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
