import NLS.Articles.KdVConvexity.ActionEmbedding

/-! # Exact weighted Arnold-action norm from a positive Hilbert calibration -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

theorem norm_baseActionSpace (b : BaseActionSpace) :
    ‖b‖ = ∑' n : ℕ+, ‖b.val (actionIndexEquiv.symm n)‖/(1+(n : ℝ)) := by
  change ‖WeightedCoeff.weightEquiv baseActionWeight 1 b‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one,one_div_one,Real.rpow_one,
    WeightedCoeff.weightEquiv_apply,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (baseActionWeight.positive _).le]
  have he := actionIndexEquiv.tsum_eq (fun n : ℕ+ =>
    (1+(n : ℝ))⁻¹*‖b.val (actionIndexEquiv.symm n)‖)
  simpa only [baseActionWeight,Equiv.symm_apply_apply,div_eq_mul_inv,mul_comm] using he

theorem tsum_positive_norm_sq_of_supported (a : Coeff 2)
    (hz : ∀ k : ℤ, k ≤ 0 → a k = 0) :
    (∑' n : ℕ+, ‖a (n : ℤ)‖^2) = ‖a‖^2 := by
  have hi : Function.Injective (fun n : ℕ+ => (n : ℤ)) := by
    intro n m h
    apply Subtype.ext
    exact Int.ofNat.inj h
  have he := hi.tsum_eq (f := fun k : ℤ => ‖a k‖^2) (by
    intro k hk
    have hkpos : 0 < k := by
      by_contra h
      have he := hz k (by omega)
      simp only [Function.mem_support,ne_eq,he,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),not_true_eq_false] at hk
    exact ⟨⟨k.toNat,by omega⟩,by change (k.toNat : ℤ) = k; omega⟩)
  have hn : ‖a‖^2 = ∑' k : ℤ, ‖a k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
  exact he.trans hn.symm

theorem norm_action_eq_positive_norm_sq (b : BaseActionSpace) (a : Coeff 2)
    (hz : ∀ k : ℤ, k ≤ 0 → a k = 0)
    (hcal : ∀ n : ℕ+, b.val (actionIndexEquiv.symm n) =
      (((1+(n : ℝ))*‖a (n : ℤ)‖^2 : ℝ) : ℂ)) :
    ‖b‖ = ‖a‖^2 := by
  rw [norm_baseActionSpace]
  calc
    (∑' n : ℕ+, ‖b.val (actionIndexEquiv.symm n)‖/(1+(n : ℝ))) =
        ∑' n : ℕ+, ‖a (n : ℤ)‖^2 := by
      apply tsum_congr
      intro n
      rw [hcal n,norm_real,Real.norm_of_nonneg (by positivity)]
      exact mul_div_cancel_left₀ _ (by positivity : 1+(n : ℝ) ≠ 0)
    _ = _ := tsum_positive_norm_sq_of_supported a hz

end NLS.Articles.KdVConvexity
