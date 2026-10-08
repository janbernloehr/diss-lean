import NLS.ZakharovShabat.FiniteGapPacking

/-! # Finite complex gaps in a horizontal strip

Global ordering bounds the sum of squared real displacements. Height at
most one bounds the imaginary contribution by four per endpoint pair.
-/
noncomputable section
namespace NLS.ZakharovShabat

/-- Complex gaps in a unit-height strip satisfy a finite-width estimate with a cardinality term. -/
theorem sum_gap_sq_le_of_height_one (s : Finset ℤ) (ξ η : ℤ → ℂ) (a b : ℝ)
    (hab : a ≤ b)
    (hb : ∀ n ∈ s, a ≤ (ξ n).re ∧ (ξ n).re ≤ (η n).re ∧ (η n).re ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → (η i).re ≤ (ξ j).re)
    (hh : ∀ n ∈ s, |(ξ n).im| ≤ 1 ∧ |(η n).im| ≤ 1) :
    ∑ n ∈ s, ‖η n-ξ n‖^2 ≤ (b-a)^2+4*s.card := by
  have hpack := sum_ordered_interval_sq_le s (fun n => (ξ n).re) (fun n => (η n).re) a b hab hb ho
  have hs : (∑ n ∈ s, ‖η n-ξ n‖^2) ≤ ∑ n ∈ s, (((η n).re-(ξ n).re)^2+4) := by
    apply Finset.sum_le_sum
    intro n hn
    have hL := abs_le.mp (hh n hn).1
    have hR := abs_le.mp (hh n hn).2
    have hi : ((η n).im-(ξ n).im)^2 ≤ 4 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2-((η n).im-(ξ n).im))
        (by linarith : 0 ≤ 2+((η n).im-(ξ n).im))]
    have he := Complex.sq_norm_sub_sq_re (η n-ξ n)
    simp only [Complex.sub_re,Complex.sub_im] at he
    linarith
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hs
  linarith

end NLS.ZakharovShabat
