import NLS.KdV.HillSharpComplement

noncomputable section
set_option autoImplicit false
namespace NLS.Articles.KdVEstimates
open NLS.KdV

/-- The radius printed on page 26, kept distinct from the checked radius-six strip. -/
def printedAppendixAHillStrip (n : ℕ) : Set ℂ :=
  {z | |z.re-freeHillValue n| ≤ 12*(n : ℝ)}

/-- At n=1 the printed strip includes a retained zero denominator. In particular
the asserted complementary inverse does not exist on the entire printed strip. -/
theorem lemmaA3_printed_strip_obstruction :
    (0 : ℂ) ∈ printedAppendixAHillStrip 1 ∧
      (0 : ℤ).natAbs ≠ 1 ∧
      ¬ ∃ g : ℤ → ℂ, ∀ k : ℤ,
        ((0 : ℂ)-(freeHillValue k : ℂ))*g k = if k = 0 then 1 else 0 := by
  refine ⟨?_,by norm_num,?_⟩
  · have hp := Real.pi_lt_d2
    have hpos := Real.pi_pos
    norm_num only [printedAppendixAHillStrip,Set.mem_ofPred_eq,Complex.zero_re,
      freeHillValue,Int.cast_one,Nat.cast_one,one_pow,mul_one,zero_sub,abs_neg,
      abs_of_nonneg (sq_nonneg Real.pi)]
    nlinarith
  · rintro ⟨g,hg⟩
    have h := hg 0
    norm_num [freeHillValue] at h

/-- Corrected A.3 on the radius-six strips. The literal Fourier tail operator
obeys the printed constant two in every shifted norm. -/
theorem lemmaA3_corrected (w : NLS.SpectralWeight) (i : ℤ)
    (q : NLS.WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (a : NLS.WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillTailPerturbation w q n hn z hz a) ≤
      (2*‖q‖/(n : ℝ))*w.shiftedNorm i a :=
  shiftedNorm_hillTailPerturbation_le_two w i q n hn z hz a

end NLS.Articles.KdVEstimates
