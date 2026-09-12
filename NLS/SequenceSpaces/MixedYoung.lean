import NLS.SequenceSpaces.MixedYoungExponents

/-!
# Appendix B.3: the mixed three-sequence Young inequality

The two successive powered Young estimates control precisely the displayed
nested sums. All three summation levels are proved convergent. Positive real
exponents below one are included; the powered Young exponents are Banach.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Extracting a constant factor from the inner power sum gives the middle mixed term. -/
theorem mixedYoung_row_identity {α β : ℝ} (hα : 0 < α) (z : ℂ) (f : ℤ → ℂ) :
    ‖z * (((∑' m : ℤ, ‖f m‖ ^ α) ^ (1 / α) : ℝ) : ℂ)‖ ^ β =
      (∑' m : ℤ, ‖z * f m‖ ^ α) ^ (β / α) := by
  have hs : (∑' m : ℤ, ‖z * f m‖ ^ α) = ‖z‖ ^ α * ∑' m : ℤ, ‖f m‖ ^ α := by
    simp only [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), tsum_mul_left]
  rw [hs, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (tsum_nonneg (fun _ => by positivity)) _),
    Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg (tsum_nonneg (fun _ => by positivity)) _),
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _) (tsum_nonneg (fun _ => by positivity)),
    ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (tsum_nonneg (fun _ => by positivity))]
  congr 2 <;> field_simp [hα.ne']

/-- The middle sum of the mixed norm, at a fixed output frequency. -/
def mixedYoungRow (α β : ℝ) (a b c : ℤ → ℂ) (k : ℤ) : ℝ :=
  ∑' l : ℤ, (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α)

theorem mixedYoungRow_nonneg (α β : ℝ) (a b c : ℤ → ℂ) (k : ℤ) :
    0 ≤ mixedYoungRow α β a b c k :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (tsum_nonneg (fun _ => by positivity)) _)

/-- Appendix B.3, with convergence of every nested sum and the exact constant one. -/
theorem mixedYoung_summable_and_le {α β γ p₁ p₂ p₃ : ℝ}
    (h : MixedYoungRelation α β γ p₁ p₂ p₃)
    (a : Coeff (ENNReal.ofReal p₁)) (b : Coeff (ENNReal.ofReal p₂))
    (c : Coeff (ENNReal.ofReal p₃)) :
    (∀ k l : ℤ, Summable (fun m : ℤ => ‖a (k - l) * b (l - m) * c m‖ ^ α)) ∧
    (∀ k : ℤ, Summable (fun l : ℤ =>
      (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α))) ∧
    Summable (fun k : ℤ => mixedYoungRow α β a b c k ^ (γ / β)) ∧
    (∑' k : ℤ, mixedYoungRow α β a b c k ^ (γ / β)) ^ (1 / γ) ≤ ‖a‖ * ‖b‖ * ‖c‖ := by
  obtain ⟨q, hi, ho⟩ := h.exists_intermediate
  obtain ⟨d, hd, hdn⟩ := exists_powerConvolution hi b c
  obtain ⟨e, he, hen⟩ := exists_powerConvolution ho a d
  have hrow (k l : ℤ) : ‖a (k - l) * d l‖ ^ β =
      (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α) := by
    rw [hd]
    simpa only [mul_assoc] using
      mixedYoung_row_identity h.alpha_pos (a (k - l)) (fun m => b (l - m) * c m)
  have he' (k : ℤ) : e k = (mixedYoungRow α β a b c k ^ (1 / β) : ℝ) := by
    rw [he]
    simp only [hrow, mixedYoungRow]
  have hepow (k : ℤ) : ‖e k‖ ^ γ = mixedYoungRow α β a b c k ^ (γ / β) := by
    rw [he', Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (mixedYoungRow_nonneg _ _ _ _ _ _) _),
      ← Real.rpow_mul (mixedYoungRow_nonneg _ _ _ _ _ _)]
    congr 1
    ring
  have heNorm : ‖e‖ = (∑' k : ℤ, mixedYoungRow α β a b c k ^ (γ / β)) ^ (1 / γ) := by
    rw [lp.norm_eq_tsum_rpow (by simpa [ENNReal.toReal_ofReal h.gamma_pos.le] using h.gamma_pos)]
    simp only [ENNReal.toReal_ofReal h.gamma_pos.le, hepow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k l
    have hs := (summable_powerConvolution hi b c l).mul_left (‖a (k - l)‖ ^ α)
    simpa only [norm_mul,
      Real.mul_rpow (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_assoc] using hs
  · intro k
    simpa only [hrow] using summable_powerConvolution ho a d k
  · have hs := (lp.memℓp e).summable
      (by simpa [ENNReal.toReal_ofReal h.gamma_pos.le] using h.gamma_pos)
    simpa only [ENNReal.toReal_ofReal h.gamma_pos.le, hepow] using hs
  · rw [← heNorm]
    exact hen.trans ((mul_le_mul_of_nonneg_left hdn (lp.norm_nonneg' a)).trans_eq (mul_assoc _ _ _).symm)

/-- The displayed mixed Young estimate, with all exponents and all three sums explicit. -/
theorem mixedYoung_le {α β γ p₁ p₂ p₃ : ℝ} (h : MixedYoungRelation α β γ p₁ p₂ p₃)
    (a : Coeff (ENNReal.ofReal p₁)) (b : Coeff (ENNReal.ofReal p₂))
    (c : Coeff (ENNReal.ofReal p₃)) :
    (∑' k : ℤ, (∑' l : ℤ,
      (∑' m : ℤ, ‖a (k - l) * b (l - m) * c m‖ ^ α) ^ (β / α)) ^ (γ / β)) ^ (1 / γ) ≤
      ‖a‖ * ‖b‖ * ‖c‖ := (mixedYoung_summable_and_le h a b c).2.2.2

/-- Unit modes have a unit mixed row only at zero frequency. -/
theorem mixedYoungRow_unit_modes {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (k : ℤ) :
    mixedYoungRow α β (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1) k =
      if k = 0 then 1 else 0 := by
  unfold mixedYoungRow
  have hi (l : ℤ) : (∑' m : ℤ,
      ‖(Pi.single 0 (1 : ℂ) : ℤ → ℂ) (k - l) * (Pi.single 0 (1 : ℂ) : ℤ → ℂ) (l - m) *
        (Pi.single 0 (1 : ℂ) : ℤ → ℂ) m‖ ^ α) =
      ‖(Pi.single 0 (1 : ℂ) : ℤ → ℂ) (k - l) * (Pi.single 0 (1 : ℂ) : ℤ → ℂ) l‖ ^ α := by
    rw [tsum_eq_single 0 (by intro m hm; simp [Pi.single_apply, hm, Real.zero_rpow hα.ne'])]
    simp
  simp_rw [hi]
  rw [tsum_eq_single 0 (by intro l hl; simp [Pi.single_apply, hl,
    Real.zero_rpow hα.ne', Real.zero_rpow (div_pos hβ hα).ne'])]
  by_cases hk : k = 0 <;> simp [hk, Real.zero_rpow hα.ne',
    Real.zero_rpow (div_pos hβ hα).ne']

/-- Unit modes attain one in the mixed norm for every positive choice of nesting exponents. -/
theorem mixedYoung_unit_modes {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    (∑' k : ℤ, mixedYoungRow α β (Pi.single 0 1) (Pi.single 0 1) (Pi.single 0 1) k ^ (γ / β)) ^
      (1 / γ) = 1 := by
  rw [tsum_eq_single 0 (by intro k hk; simp [mixedYoungRow_unit_modes hα hβ, hk,
    Real.zero_rpow (div_pos hγ hβ).ne'])]
  simp [mixedYoungRow_unit_modes hα hβ]

end NLS.Coeff
