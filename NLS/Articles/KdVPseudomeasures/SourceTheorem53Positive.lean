import NLS.Articles.KdVPseudomeasures.SourceTheorem53

/-! The one-sided gap hypothesis printed in Theorem 5.3. The natural
index j denotes the actual positive spectral index j+1, weighted by
(j+1)^N; no additional negative-index or zero-mode premise is imposed. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem original_signed_gap_membership_of_positive_summable (N : ℕ)
    (q : OriginalHminusOnePotential)
    (hg : Summable (fun j : ℕ => ((j:ℝ)+1)^(N:ℝ)*
      ‖originalCanonicalGapValues q ((j:ℤ)+1)‖)) :
    Memℓp (fun k => (Weight.signedSobolev (N:ℝ) k:ℂ)*originalCanonicalGapValues q k) 1 := by
  have hpoint (j : ℕ) :
      ‖(Weight.signedSobolev (N:ℝ) ((j:ℤ)+1):ℂ)*originalCanonicalGapValues q ((j:ℤ)+1)‖=
        ((j:ℝ)+1)^(N:ℝ)*‖originalCanonicalGapValues q ((j:ℤ)+1)‖ := by
    rw [norm_mul,Complex.norm_real,
      Real.norm_of_nonneg ((Weight.signedSobolev (N:ℝ)).positive _).le]
    congr 1
    change (max 1 |(((j:ℤ)+1:ℤ):ℝ)|)^ (N:ℝ) = _
    have hm : (1:ℝ) ≤ (j:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) j]
    simp only [Int.cast_add,Int.cast_natCast,Int.cast_one,
      abs_of_nonneg (by positivity : 0 ≤ (j:ℝ)+1),max_eq_right hm]
  have hp : Summable (fun j : ℕ =>
      ‖(Weight.signedSobolev (N:ℝ) ((j:ℤ)+1):ℂ)*originalCanonicalGapValues q ((j:ℤ)+1)‖) :=
    hg.congr (fun j => (hpoint j).symm)
  have hn : Summable (fun j : ℕ =>
      ‖(Weight.signedSobolev (N:ℝ) (-((j:ℤ)+1)):ℂ)*originalCanonicalGapValues q (-((j:ℤ)+1))‖) := by
    simpa only [Weight.signedSobolev_neg,originalCanonicalGapValues_neg] using hp
  have hs : Summable (fun k : ℤ =>
      ‖(Weight.signedSobolev (N:ℝ) k:ℂ)*originalCanonicalGapValues q k‖) :=
    Summable.of_add_one_of_neg_add_one hp hn
  rw [memℓp_gen_iff (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_one,Real.rpow_one] using hs

/-- Theorem 5.3 with only the printed positive gap-length hypothesis.
The conclusion is proved on the entire real H-minus-one domain and thus
includes the printed real mean-zero L2 domain. -/
theorem sourceTheorem5_3 (N : ℕ) (q : OriginalHminusOnePotential)
    (hg : Summable (fun j : ℕ => ((j:ℝ)+1)^(N:ℝ)*
      ‖originalCanonicalGapValues q ((j:ℤ)+1)‖)) :
    (∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=q) ∧
      ∀ v : OriginalHminusOnePotential, v ∈ originalIsospectralSet q →
        ∃ p : OriginalWienerPotential N, originalWienerOriginalPotential N p=v :=
  sourceTheorem5_3_signed N q (original_signed_gap_membership_of_positive_summable N q hg)

end NLS.Articles.KdVPseudomeasures
