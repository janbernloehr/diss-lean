import NLS.Articles.KdVPseudomeasures.OriginalCanonicalGapSquares
import NLS.KdV.HillHminusOneCanonicalQuotients

/-! # The action assertions of source Theorem 3.2 on the original domain

ALL canonical action/squared-gap quotients extend analytically and
nonvanishingly to ONE connected complex neighborhood of the entire
original real mean-zero H-minus-one domain. Normalization is locally
uniform at EVERY complex point, and complex action and squared-gap zero
sets agree at ALL positive indices. The Birkhoff-coordinate assertion
(ii), the Birkhoff-map identity Phi(0)=0 and the five MAIN theorems are
not consequences claimed here. The printed Z_n complement is corrected:
the literal quotient is asserted where the squared gap is NONZERO.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

def originalCanonicalHillActionQuotient (n : ℕ+) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusCanonicalActionQuotient n (originalPeriodOneCoefficients q)

theorem originalCanonicalHillActionQuotient_ne_zero (n : ℕ+) (q : OriginalHminusOnePotential) :
    originalCanonicalHillActionQuotient n q ≠ 0 :=
  hillHminusCanonicalActionQuotient_ne_zero n _
    (real_mem_hillHminusCanonicalRatioDomain _ (originalPeriodOneCoefficients_real q))

theorem originalCanonicalHillAction_eq_gapSquare_mul_quotient (n : ℕ+) (q : OriginalHminusOnePotential) :
    originalCanonicalHillAction n q =
      originalCanonicalGapValues q (n : ℕ)^2*originalCanonicalHillActionQuotient n q := by
  have he := hillHminusCanonicalAction_eq_gapSquare_mul_quotient n (originalPeriodOneCoefficients q)
    (real_mem_hillHminusCanonicalRatioDomain _ (originalPeriodOneCoefficients_real q))
  rw [originalCanonicalGapSquare_eq] at he
  exact he

theorem originalCanonicalHillActionQuotient_eq_raw (n : ℕ+) (q : OriginalHminusOnePotential)
    (hg : originalCanonicalGapValues q (n : ℕ) ≠ 0) :
    originalCanonicalHillActionQuotient n q = originalCanonicalHillAction n q/originalCanonicalGapValues q (n : ℕ)^2 := by
  rw [originalCanonicalHillAction_eq_gapSquare_mul_quotient n q]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero 2 hg)).symm

theorem source_Theorem3_2_action_assertions :
    ∃ W : Set PeriodOneHminusOne, IsOpen W ∧ IsConnected W ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ W) ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalAction n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalGapSquare n) W ∧
        AnalyticOnNhd ℂ (hillHminusCanonicalActionQuotient n) W ∧
        ∀ a ∈ W, hillHminusCanonicalActionQuotient n a ≠ 0 ∧
          hillHminusCanonicalAction n a = hillHminusCanonicalGapSquare n a*hillHminusCanonicalActionQuotient n a ∧
          (hillHminusCanonicalAction n a = 0 ↔ hillHminusCanonicalGapSquare n a = 0) ∧
          (hillHminusCanonicalGapSquare n a ≠ 0 →
            hillHminusCanonicalActionQuotient n a = hillHminusCanonicalAction n a/hillHminusCanonicalGapSquare n a)) ∧
      ∀ a ∈ W, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ W ∧
          ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ b ∈ U,
            ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusCanonicalActionQuotient n b-1‖ ≤ epsilon := by
  refine ⟨hillHminusCanonicalRatioDomain,isOpen_hillHminusCanonicalRatioDomain,
    isConnected_hillHminusCanonicalRatioDomain,
    (fun q => real_mem_hillHminusCanonicalRatioDomain _ (originalPeriodOneCoefficients_real q)),?_,
    exists_hillHminusCanonicalActionQuotient_uniform_high⟩
  intro n
  refine ⟨analyticOnNhd_hillHminusCanonicalAction_on_ratioDomain n,
    analyticOnNhd_hillHminusCanonicalGapSquare_on_ratioDomain n,
    analyticOnNhd_hillHminusCanonicalActionQuotient n,?_⟩
  intro a ha
  exact ⟨hillHminusCanonicalActionQuotient_ne_zero n a ha,
    hillHminusCanonicalAction_eq_gapSquare_mul_quotient n a ha,
    hillHminusCanonicalAction_eq_zero_iff_gapSquare n a ha,
    hillHminusCanonicalActionQuotient_eq_raw n a ha⟩

end NLS.Articles.KdVPseudomeasures
