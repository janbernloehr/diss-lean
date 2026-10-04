import NLS.ZakharovShabat.SourceAbelianMomentOffDiagonalMajorants

/-! # Actual cubic-gap coefficients for off-diagonal second moments

The normalized coefficient is defined directly from the actual moment,
with zero at the deleted index and the totalized quotient at closed gaps.
The cubic majorant proves its refined sequence membership and uniform norm
bound. The exact factorization remains valid at collapsed selected gaps.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual off-diagonal cubic-gap coefficient, independent of the
sequence exponent and of the neighborhood used to bound it. -/
def sourceSecondMomentCubicCoefficient (A : SourceAbelianMomentAtlas hp hp1 W s)
    (n : ℤ) (ψ : CoeffPair p) (k : ℤ) : ℂ :=
  if k = n then 0 else ((n-k:ℤ):ℂ)*A.moment n k 2 ψ /
    (sourcePeriodicGapDisplacement hp hp1 ψ k)^3

variable {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- A cubic-gap row bound constructs the actual coefficient sequence,
including its exact factorization at zero gaps. -/
theorem exists_secondMoment_cubic_coeff_of_majorant
    (ψ : CoeffPair p) (n : ℤ) {r : ℝ≥0∞} (hr0 : r ≠ 0) (B : Coeff r)
    (hbound : ∀ k : ℤ, k ≠ n → ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*‖B k‖) :
    ∃ a : Coeff r, (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧
      a n = 0 ∧ ‖a‖ ≤ ‖B‖ ∧ ∀ k : ℤ, k ≠ n →
        A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
  have hpoint (k : ℤ) : ‖sourceSecondMomentCubicCoefficient A n ψ k‖ ≤ ‖B k‖ := by
    unfold sourceSecondMomentCubicCoefficient
    split_ifs with hkn
    · exact (norm_zero).le.trans (norm_nonneg _)
    · by_cases hγ : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
      · simp only [hγ,zero_pow (by norm_num : (3:ℕ) ≠ 0),div_zero,norm_zero]
        exact norm_nonneg _
      · rw [norm_div,norm_pow]
        apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hγ) 3)).mpr
        simpa only [mul_comm] using hbound k hkn
  let a : Coeff r := ⟨sourceSecondMomentCubicCoefficient A n ψ,(lp.memℓp B).mono' hpoint⟩
  refine ⟨a,fun k => rfl,?_,lp.norm_mono hr0 hpoint,?_⟩
  · simp only [a,sourceSecondMomentCubicCoefficient,ite_true]
  · intro k hkn
    have hnk : ((n-k:ℤ):ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hkn.symm
    by_cases hγ : sourcePeriodicGapDisplacement hp hp1 ψ k = 0
    · have hb := hbound k hkn
      simp only [hγ,norm_zero,zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_mul] at hb
      have hz := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
      have hm := (mul_eq_zero.mp hz).resolve_left hnk
      simp only [hm,hγ,zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_div,zero_mul]
    · change _ = _*sourceSecondMomentCubicCoefficient A n ψ k
      simp only [sourceSecondMomentCubicCoefficient,if_neg hkn]
      field_simp

/-- Around each real source, the exact cubic-gap coefficient has uniformly
bounded refined row norms, on one neighborhood preceding the exponent. -/
theorem SourceAbelianMomentErrorDomain.exists_local_offDiagonal_secondMoment_coefficients
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφV : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ D.domain ∩ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ a : Coeff r,
          (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧
          a n = 0 ∧ ‖a‖ ≤ M ∧ ∀ k : ℤ, k ≠ n →
            A.moment n k 2 ψ = (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k := by
  obtain ⟨T,hT,hφT,hTV,hmajor⟩ := D.exists_local_offDiagonal_secondMoment_majorants hs φ hφV
  refine ⟨T,hT,hφT,hTV,?_⟩
  intro r hr hr1 hpr
  obtain ⟨M,hM,hrows⟩ := hmajor r hr hr1 hpr
  refine ⟨M,hM,?_⟩
  intro ψ hψ n
  obtain ⟨B,hB,hbound⟩ := hrows ψ hψ n
  obtain ⟨a,ha,han,haB,hfactor⟩ := exists_secondMoment_cubic_coeff_of_majorant ψ n
    (zero_lt_one.trans hr1).ne' B hbound
  exact ⟨a,ha,han,haB.trans hB,hfactor⟩

end NLS.ZakharovShabat
