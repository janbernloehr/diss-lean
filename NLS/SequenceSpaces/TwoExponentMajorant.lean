import NLS.SequenceSpaces.FiniteModification
import NLS.SequenceSpaces.SandwichMajorant
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-!
# Tail majorants from two sequence exponents

A scalar sequence whose distant coordinates are bounded by the sum of
an `ℓq` sequence and an `ℓr` sequence belongs to `ℓq` whenever
`0 < r ≤ q`. This includes the quasi-Banach range `r < 1`.
The tail has a norm bound by the two majorant norms, and the finitely
many unconstrained central coordinates do not affect membership.
-/

noncomputable section
open scoped ENNReal
namespace NLS
namespace Coeff
variable {r q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Two pointwise sequence majorants control an `ℓq` tail and put the
entire scalar sequence in `ℓq`, including when the second exponent is
below one. -/
theorem exists_tailCoeff_of_twoSequenceMajorants
    (hr : 0 < r) (hq1 : 1 < q) (hq : q ≠ ⊤) (hrq : r ≤ q)
    (a : ℤ → ℂ) (K : ℕ) (A : Coeff q) (B : Coeff r)
    (hpoint : ∀ n : ℤ, K ≤ n.natAbs →
      ‖a n‖ ≤ ‖A n‖ + ‖B n‖) :
    ∃ T : Coeff q,
      (∀ n : ℤ, T n = if K ≤ n.natAbs then a n else 0) ∧
      ‖T‖ ≤ ‖A‖ + ‖B‖ ∧ Memℓp a q := by
  let Bq : Coeff q := ⟨fun n => B n,(lp.memℓp B).of_exponent_ge hrq⟩
  let M : Coeff q := magnitude A + magnitude Bq
  have hMpoint (n : ℤ) : ‖M n‖ = ‖A n‖ + ‖B n‖ := by
    simp only [M,lp.coeFn_add,Pi.add_apply,magnitude_apply,Bq]
    rw [← Complex.ofReal_add, Complex.norm_real]
    exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hTmem : Memℓp (fun n : ℤ => if K ≤ n.natAbs then a n else 0) q :=
    (lp.memℓp M).mono' (by
      intro n
      by_cases hn : K ≤ n.natAbs
      · simpa only [if_pos hn,hMpoint n] using hpoint n hn
      · simp only [if_neg hn,norm_zero]
        exact norm_nonneg _)
  let T : Coeff q := ⟨fun n => if K ≤ n.natAbs then a n else 0,hTmem⟩
  have hTleM : ‖T‖ ≤ ‖M‖ :=
    lp.norm_mono (zero_lt_one.trans hq1).ne' (by
      intro n
      by_cases hn : K ≤ n.natAbs
      · simpa only [T,if_pos hn,hMpoint n] using hpoint n hn
      · simp only [T,if_neg hn,norm_zero]
        exact norm_nonneg _)
  have hBqnorm : ‖Bq‖ ≤ ‖B‖ :=
    norm_quasiExponentInclusion_le hr (zero_lt_one.trans hq1) hq hrq B
  have hMnorm : ‖M‖ ≤ ‖A‖ + ‖Bq‖ := by
    calc
      ‖M‖ ≤ ‖magnitude A‖ + ‖magnitude Bq‖ := norm_add_le _ _
      _ = ‖A‖ + ‖Bq‖ := by simp
  have hfull : Memℓp a q := by
    let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
    apply memℓp_of_eq_outside_finset hTmem s
    intro n hn
    have hKn : K ≤ n.natAbs := by
      simp only [s,Finset.mem_Icc] at hn
      omega
    simp only [if_pos hKn]
  refine ⟨T,fun n => rfl,?_,hfull⟩
  exact hTleM.trans (hMnorm.trans (add_le_add_right hBqnorm _))

end Coeff
end NLS
