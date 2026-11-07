import NLS.KdV.HillHminusOneCanonicalNormalizedActions

/-! # The canonical quotient I_n/gamma_n² and its uniform normalization

ALL quotients are analytic and nonzero on the SAME open connected complex
domain. Their literal values away from zero gaps, exact factorizations,
and locally uniform 8*pi*n normalization hold for the canonical Hill
actions and the ALL-index canonical squared gaps, including collapse.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

def hillHminusCanonicalActionQuotient (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusCanonicalActionRatio n q/(8*((Real.pi : ℂ)*(n : ℕ)))

theorem analyticOnNhd_hillHminusCanonicalActionQuotient (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalActionQuotient n) hillHminusCanonicalRatioDomain :=
  fun q hq => (analyticOnNhd_hillHminusCanonicalActionRatio n q hq).div_const

theorem hillHminusCanonicalActionQuotient_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) : hillHminusCanonicalActionQuotient n q ≠ 0 := by
  exact div_ne_zero (hillHminusCanonicalActionRatio_ne_zero n q hq)
    (mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero)))

theorem hillHminusCanonicalAction_eq_gapSquare_mul_quotient (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) :
    hillHminusCanonicalAction n q = hillHminusCanonicalGapSquare n q*hillHminusCanonicalActionQuotient n q := by
  rw [hillHminusCanonicalAction_gap_factorization n q hq,hillHminusCanonicalActionQuotient]
  ring

theorem hillHminusCanonicalActionQuotient_eq_raw (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusCanonicalActionQuotient n q = hillHminusCanonicalAction n q/hillHminusCanonicalGapSquare n q := by
  rw [hillHminusCanonicalAction_eq_gapSquare_mul_quotient n q hq]
  exact (mul_div_cancel_left₀ _ hg).symm

theorem hillHminusCanonicalActionRatio_eq_normalized_quotient (n : ℕ+) (q : PeriodOneHminusOne) :
    hillHminusCanonicalActionRatio n q =
      (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalActionQuotient n q := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  unfold hillHminusCanonicalActionQuotient
  field_simp [hK]

theorem exists_hillHminusCanonicalActionRatio_uniform_high
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalRatioDomain)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalRatioDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ U, ‖hillHminusCanonicalActionRatio n a-1‖ ≤ epsilon := by
  obtain ⟨N,V,hN,hV,hqV,_,hdata⟩ := exists_hillHminus_canonical_gap_high_normalization_at_complex q
    (hillHminusCanonicalRatioDomain_subset hq) epsilon hepsilon
  let U := V ∩ hillHminusCanonicalRatioDomain
  have hU : IsOpen U := hV.inter isOpen_hillHminusCanonicalRatioDomain
  refine ⟨N,U,hN,hU,⟨hqV,hq⟩,inter_subset_right,?_⟩
  intro n hn
  by_cases hz : ∀ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a = 0
  · intro a _
    simp only [hillHminusCanonicalActionRatio,if_pos hz,sub_self,norm_zero]
    exact hepsilon.le
  · have hne : ∃ a ∈ hillHminusCanonicalRatioDomain, hillHminusCanonicalGapSquare n a ≠ 0 := by simpa using hz
    have heq : EqOn (hillHminusCanonicalActionRatio n) (hillHminusGluedHighActionRatio n) U :=
      hillHminusCanonicalActionRatio_unique_on_open n U hU inter_subset_right _
        ((hdata n hn).1.mono inter_subset_left) hne
        (fun a ha => ((hdata n hn).2 a ha.1).2.2.1)
    intro a ha
    rw [heq ha]
    exact ((hdata n hn).2 a ha.1).1

theorem exists_hillHminusCanonicalActionQuotient_uniform_high
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalRatioDomain)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalRatioDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ U,
        ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalActionQuotient n a-1‖ ≤ epsilon := by
  obtain ⟨N,U,hN,hU,hqU,hUD,hdata⟩ := exists_hillHminusCanonicalActionRatio_uniform_high q hq epsilon hepsilon
  refine ⟨N,U,hN,hU,hqU,hUD,?_⟩
  intro n hn a ha
  rw [← hillHminusCanonicalActionRatio_eq_normalized_quotient]
  exact hdata n hn a ha

theorem norm_hillHminusCanonicalAction_error_le (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalRatioDomain) (epsilon : ℝ)
    (hR : ‖hillHminusCanonicalActionRatio n q-1‖ ≤ epsilon) :
    ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n q-hillHminusCanonicalGapSquare n q‖ ≤
      ‖hillHminusCanonicalGapSquare n q‖*epsilon := by
  have hK : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  have he : (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalAction n q-hillHminusCanonicalGapSquare n q =
      hillHminusCanonicalGapSquare n q*(hillHminusCanonicalActionRatio n q-1) := by
    rw [hillHminusCanonicalAction_gap_factorization n q hq]
    field_simp [hK]
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)

end NLS.KdV
