import NLS.ZakharovShabat.BirkhoffSobolevNormArithmetic

/-! # Theorem 23.1: two-sided estimates for the actual real Birkhoff map -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Theorem 23.1 for every constructed Birkhoff map, with exact physical norms
and strictly positive constants uniform over the entire real H^m source. -/
theorem exists_sobolev_two_sided_bounds
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      (‖D.sobolevCoordinates m hm m le_rfl a‖ ≤ c*
        (‖sourcePiSobolevCoordinates m m le_rfl a.val‖+
          (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(2*m)*‖higherSobolevSourceInclusion m a.val‖)) ∧
      (‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ d*
        (‖D.sobolevCoordinates m hm m le_rfl a‖+
          (1+‖D.sobolevCoordinates m hm 1 hm a‖)^(4*m-3)*‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖)) := by
  obtain ⟨c,hc,hupper⟩ := exists_sourceWeightedAction_sobolev_upper_bound m hm
  obtain ⟨d,hd,hlower⟩ := exists_sourceSobolev_weightedAction_lower_bound m hm
  refine ⟨2*c+1,2*d+1,by positivity,by positivity,?_⟩
  intro a
  let φ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  let T := ∑' n : ℤ, sourceWeightedActionTerm φ m n
  let S := ∑' n : ℤ, sourceWeightedActionTerm φ 1 n
  let M := ∑' n : ℤ, sourceWeightedActionTerm φ 0 n
  let P := ‖sourcePiSobolevCoordinates m m le_rfl a.val‖
  let P1 := ‖sourcePiSobolevCoordinates m 1 hm a.val‖
  let P0 := ‖higherSobolevSourceInclusion m a.val‖
  let Q := ‖D.sobolevCoordinates m hm m le_rfl a‖
  let Q1 := ‖D.sobolevCoordinates m hm 1 hm a‖
  let Q0 := ‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖
  have hP : 0 ≤ P := norm_nonneg _
  have hP1 : 0 ≤ P1 := norm_nonneg _
  have hP0 : 0 ≤ P0 := norm_nonneg _
  have hQ : 0 ≤ Q := norm_nonneg _
  have hQ1 : 0 ≤ Q1 := norm_nonneg _
  have hQ0 : 0 ≤ Q0 := norm_nonneg _
  have hnon (k : ℕ) : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm φ k n := by
    apply tsum_nonneg
    intro n
    unfold sourceWeightedActionTerm
    positivity
  have hT : 0 ≤ T := hnon m
  have hS : 0 ≤ S := hnon 1
  have hM : 0 ≤ M := hnon 0
  have hQT : Q^2 = 2*T := D.sobolevCoordinates_norm_sq m hm m le_rfl a
  have hQ1S : Q1^2 = 2*S := D.sobolevCoordinates_norm_sq m hm 1 hm a
  have hQ0M : Q0^2 = 2*M := D.sobolevCoordinates_norm_sq m hm 0 (Nat.zero_le m) a
  constructor
  · let R := (1+P1)^(2*m)*P0
    have hR : 0 ≤ R := by positivity
    have he : R^2 = (1+P1)^(4*m)*P0^2 := by
      dsimp [R]
      rw [mul_pow,← pow_mul,show 2*m*2 = 4*m by omega]
    have h := hupper a
    change T ≤ c^2*(P^2+(1+P1)^(4*m)*P0^2) at h
    rw [← he] at h
    exact norm_bound_of_two_squared_terms Q P R c hQ hP hR hc (by nlinarith)
  · let R := (1+Q1)^(4*m-3)*Q0
    have hR : 0 ≤ R := by positivity
    have hrem : (1+S)^(4*m-3)*M ≤ R^2 :=
      action_remainder_le_birkhoff_norm_sq (4*m-3) S M Q1 Q0 hS hM hQ1 hQ1S hQ0M
    have hTQ : T ≤ Q^2 := by nlinarith
    have hs := mul_le_mul_of_nonneg_left (add_le_add hTQ hrem) (sq_nonneg d)
    have h := hlower a
    change P^2 ≤ d^2*(T+(1+S)^(4*m-3)*M) at h
    have hbound : P^2 ≤ 2*d^2*(Q^2+R^2) := by
      nlinarith [mul_nonneg (sq_nonneg d) (add_nonneg (sq_nonneg Q) (sq_nonneg R))]
    exact norm_bound_of_two_squared_terms P Q R d hP hQ hR hd hbound

end SourceBirkhoffMapComplexData

/-- A single existing Birkhoff map satisfies Theorem 23.1 simultaneously
at every positive integer Sobolev order. -/
theorem exists_sourceBirkhoffMap_sobolev_two_sided :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
      ∀ m : ℕ, ∀ hm : 1 ≤ m, ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
        ∀ a : realTypeHigherSobolevSourceLocus m,
          (‖D.sobolevCoordinates m hm m le_rfl a‖ ≤ c*
            (‖sourcePiSobolevCoordinates m m le_rfl a.val‖+
              (1+‖sourcePiSobolevCoordinates m 1 hm a.val‖)^(2*m)*‖higherSobolevSourceInclusion m a.val‖)) ∧
          (‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ d*
            (‖D.sobolevCoordinates m hm m le_rfl a‖+
              (1+‖D.sobolevCoordinates m hm 1 hm a‖)^(4*m-3)*‖D.sobolevCoordinates m hm 0 (Nat.zero_le m) a‖)) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : (1:ℝ≥0∞) < 2)
  exact ⟨W₀,B,W,s,D,fun m hm => D.exists_sobolev_two_sided_bounds m hm⟩

end NLS.ZakharovShabat
