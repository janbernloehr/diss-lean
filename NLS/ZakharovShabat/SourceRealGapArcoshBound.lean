import NLS.ZakharovShabat.SourceRealGapArcoshPrimitive

/-! # Quantitative bounds for the real gap-side arcosh profile

The profile is bounded by the positive discriminant square root. The
exact deleted-product factorization then bounds it by half the gap
length times the square root of a deleted-product bound.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The half-discriminant is at least one on the whole closed gap,
including collapsed gaps. -/
theorem realGapHalfDiscriminant_one_le_on_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    1 ≤ realGapHalfDiscriminant hp (periodOnePotential φ) n x := by
  obtain ⟨_,_,_,ha,hb,hgt⟩ := realGapHalfDiscriminant_arcosh_gap_data hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h,ha]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h',hb]
  · exact (hgt x ⟨h,h'⟩).le

/-- The arcosh profile never exceeds its positive square-root radicand. -/
theorem sourceRealGapArcoshProfile_le_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re) :
    0 ≤ sourceRealGapArcoshProfile hp φ n x ∧
      sourceRealGapArcoshProfile hp φ n x ≤
        Real.sqrt ((realGapHalfDiscriminant hp (periodOnePotential φ) n x)^2-1) := by
  have hg := realGapHalfDiscriminant_one_le_on_gap hp hp1 φ hφ n x hx
  refine ⟨Real.arcosh_nonneg hg,?_⟩
  rw [← Real.sinh_arcosh hg]
  exact Real.self_le_sinh_iff.mpr (Real.arcosh_nonneg hg)

/-- A bound on the deleted periodic product gives an explicit bound
linear in the actual gap length, valid also at both endpoints. -/
theorem sourceRealGapArcoshProfile_le_halfGap_mul_sqrt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x K : ℝ) (hK : 0 ≤ K)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)
    (hbound : (canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n x).re ≤ K) :
    sourceRealGapArcoshProfile hp φ n x ≤
      ((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 * Real.sqrt K := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  have hprod : 0 ≤ (x-a)*(b-x) := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  have hwidth : 0 ≤ (b-a)/2 := by dsimp only [a,b]; linarith [hx.1,hx.2]
  have hrad := realGapHalfDiscriminant_sq_sub_one_eq_deletedPair_re hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n x
  have hle : (realGapHalfDiscriminant hp (periodOnePotential φ) n x)^2-1 ≤ ((b-a)/2)^2*K := by
    rw [hrad]
    apply (mul_le_mul_of_nonneg_left hbound hprod).trans
    apply mul_le_mul_of_nonneg_right _ hK
    nlinarith [sq_nonneg (x-(a+b)/2)]
  apply (sourceRealGapArcoshProfile_le_sqrt hp hp1 φ hφ n x hx).2.trans
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg hwidth (Real.sqrt_nonneg K),?_⟩
  simpa only [mul_pow,Real.sq_sqrt hK] using hle

/-- Every fixed source and gap admits a finite deleted-product bound
on its whole closed interval; no bound is supplied by the caller. -/
theorem exists_sourceRealGapArcoshProfile_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re,
      sourceRealGapArcoshProfile hp φ n x ≤
        ((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re -
          (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 * Real.sqrt K := by
  let G : ℝ → ℝ := fun x => (canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n x).re
  have hG : Continuous G := continuous_re.comp
    ((continuousOn_univ.mp (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n).continuousOn).comp continuous_ofReal)
  obtain ⟨K,hK⟩ := (isCompact_Icc.image hG).bddAbove
  refine ⟨max K 0,le_max_right _ _,?_⟩
  intro x hx
  exact sourceRealGapArcoshProfile_le_halfGap_mul_sqrt hp hp1 φ hφ n x (max K 0)
    (le_max_right _ _) hx ((hK (mem_image_of_mem G hx)).trans (le_max_left _ _))

end NLS.ZakharovShabat
