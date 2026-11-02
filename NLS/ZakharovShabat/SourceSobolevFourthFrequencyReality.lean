import NLS.ZakharovShabat.SourceSobolevFourthFrequency

/-! # Reality of the independently defined physical H₄ derivatives

Both derivative branches take real values because their actual physical
Hamiltonian curves are real. This proof uses neither an Abelian moment formula
nor a choice of the article's extended normalized frequency.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ZakharovShabat

private theorem real_curve_deriv_im_zero (f : ℝ → ℂ) (hr : ∀ t, (f t).im = 0) (t : ℝ) :
    (deriv f t).im = 0 := by
  by_cases hf : DifferentiableAt ℝ f t
  · have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
    have he : (fun x => (f x).im) = fun _ : ℝ => (0:ℝ) := funext hr
    change HasDerivAt (fun x => (f x).im) (deriv f t).im t at hd
    rw [he] at hd
    exact hd.unique (hasDerivAt_const t (0:ℝ))
  · rw [deriv_zero_of_not_differentiableAt hf]
    rfl

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Every independent physical H₄ frequency is real on its full original
fractional source, including the second-derivative closed-action branch. -/
theorem sobolevFourthFrequency_im_eq_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) : (D.sobolevFourthFrequency a n).im = 0 := by
  unfold sobolevFourthFrequency
  split_ifs
  · exact real_curve_deriv_im_zero (deriv (D.sobolevFourthOpeningHamiltonian a n))
      (fun t => real_curve_deriv_im_zero (D.sobolevFourthOpeningHamiltonian a n)
        (fun r => sourceSobolevFourthHamiltonian_im_eq_zero _) t) 0
  · change (-deriv (D.sobolevFourthActionReductionHamiltonian a n) 0).im = 0
    rw [Complex.neg_im,real_curve_deriv_im_zero (D.sobolevFourthActionReductionHamiltonian a n)
      (fun t => sourceSobolevFourthHamiltonian_im_eq_zero _) 0,neg_zero]

/-- The actual real frequency embeds back into the same physical derivative. -/
theorem sobolevFourthFrequency_ofReal_re
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    ((D.sobolevFourthFrequency a n).re : ℂ) = D.sobolevFourthFrequency a n := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using (D.sobolevFourthFrequency_im_eq_zero a n).symm

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
