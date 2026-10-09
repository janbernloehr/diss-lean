import NLS.SequenceSpaces.ReciprocalNorm

/-! # Retaining the conjugate exponent in reciprocal norm estimates

The power-sum coefficient is kept before its q-th root is taken. This avoids
the earlier replacement by 2p, and permits sharper spectral-height bounds.
-/
noncomputable section
open scoped ENNReal

namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

omit [Fact (1 ≤ q)] in
/-- A reciprocal envelope with its central coefficient removed has norm at most
`2C * h^(-1/p)` when C bounds the exact conjugate-power coefficient. -/
theorem norm_punctured_reciprocal_le_of_power_bound {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hh : 0 < h) (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : 2/(q.toReal-1) ≤ C^q.toReal) (a : Coeff q) (ha0 : a 0 = 0)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2 / (h + |(k : ℝ)|)) :
    ‖a‖ ≤ 2 * C * h ^ (-(1 / p)) := by
  have hq := hc.symm.pos
  have hs := ReciprocalSeries.summable_int_shifted_rpow hh.le hc.symm.lt
  have hexp : -(1 / p) * q.toReal = 1 - q.toReal := by
    calc
      _ = -(q.toReal / p) := by ring
      _ = _ := by rw [hc.symm.div_conj_eq_sub_one]; ring
  apply lp.norm_le_of_tsum_le hq (by positivity)
  calc
    (∑' k : ℤ, ‖a k‖ ^ q.toReal) ≤
        ∑' k : ℤ, (2 : ℝ) ^ q.toReal *
          (if k = 0 then 0 else (h + |(k : ℝ)|) ^ (-q.toReal)) := by
      apply Summable.tsum_le_tsum _ ((lp.memℓp a).summable hq) (hs.mul_left _)
      intro k
      by_cases hk : k = 0
      · simp [hk, ha0, hq.ne']
      · rw [if_neg hk]
        calc
          _ ≤ (2 / (h + |(k : ℝ)|)) ^ q.toReal :=
            Real.rpow_le_rpow (norm_nonneg _) (ha k hk) hq.le
          _ = _ := by
            rw [div_eq_mul_inv, Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by positivity),
              Real.inv_rpow (by positivity : 0 ≤ h + |(k : ℝ)|),
              Real.rpow_neg (by positivity : 0 ≤ h + |(k : ℝ)|)]

    _ = (2 : ℝ) ^ q.toReal * ∑' k : ℤ,
        (if k = 0 then 0 else (h + |(k : ℝ)|) ^ (-q.toReal)) := tsum_mul_left
    _ ≤ (2 : ℝ) ^ q.toReal * (2 / (q.toReal - 1) * h ^ (1 - q.toReal)) :=
      mul_le_mul_of_nonneg_left (ReciprocalSeries.tsum_int_shifted_rpow_le_integral hh hc.symm.lt)
        (by positivity)
    _ ≤ (2 : ℝ) ^ q.toReal * (C ^ q.toReal * h ^ (1 - q.toReal)) := by
      gcongr
    _ = (2 * C * h ^ (-(1 / p))) ^ q.toReal := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * C) (by positivity),
        ← Real.rpow_mul hh.le, hexp, ← mul_assoc, ← Real.mul_rpow (by norm_num) (by positivity)]

/-- Add the central `1/h` contribution to the reciprocal-envelope bound. -/
theorem norm_reciprocal_le_of_power_bound {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hh : 0 < h) (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : 2/(q.toReal-1) ≤ C^q.toReal) (a : Coeff q) (ha0 : ‖a 0‖ ≤ h⁻¹)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2 / (h + |(k : ℝ)|)) :
    ‖a‖ ≤ 2 * C / h ^ (1 / p) + h⁻¹ := by
  let c : Coeff q := lp.single q 0 (a 0)
  let b : Coeff q := a - c
  have hb_apply (k : ℤ) : b k = a k - c k := rfl
  have hc0 : c 0 = a 0 := lp.single_apply_self _ _ _
  have hb0 : b 0 = 0 := by rw [hb_apply, hc0, sub_self]
  have hb : ∀ k : ℤ, k ≠ 0 → ‖b k‖ ≤ 2 / (h + |(k : ℝ)|) := by
    intro k hk
    have hck : c k = 0 := lp.single_apply_ne _ _ _ hk
    rw [hb_apply, hck, sub_zero]
    exact ha k hk
  have hn := norm_punctured_reciprocal_le_of_power_bound hc hh C hC hcoeff b hb0 hb
  have he : a = c + b := by dsimp only [b]; abel
  have hcnorm : ‖c‖ = ‖a 0‖ := lp.norm_single (zero_lt_one.trans_le (show 1 ≤ q from Fact.out)) _ _
  calc
    ‖a‖ = ‖c + b‖ := congrArg norm he
    _ ≤ ‖c‖ + ‖b‖ := norm_add_le _ _
    _ = ‖a 0‖ + ‖b‖ := by rw [hcnorm]
    _ ≤ h⁻¹ + 2 * C * h ^ (-(1 / p)) := add_le_add ha0 hn
    _ = _ := by rw [Real.rpow_neg hh.le]; ring

/-- The exact coefficient obtained by taking the root of the integral bound. -/
theorem norm_reciprocal_le_conjugate_root {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hh : 0 < h) (a : Coeff q) (ha0 : ‖a 0‖ ≤ h⁻¹)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2/(h+|(k : ℝ)|)) :
    ‖a‖ ≤ 2*(2/(q.toReal-1))^(1/q.toReal)/h^(1/p)+h⁻¹ := by
  have hbase : 0 < 2/(q.toReal-1) := div_pos (by norm_num) hc.symm.sub_one_pos
  apply norm_reciprocal_le_of_power_bound hc hh _ (by positivity) _ a ha0 ha
  rw [← Real.rpow_mul (by positivity : 0 ≤ 2/(q.toReal-1)),
    one_div_mul_cancel hc.symm.pos.ne',Real.rpow_one]

/-- The conjugate-power coefficient permits the constant four through p=4. -/
theorem reciprocal_power_coefficient_le_four {p q : ℝ} (hc : p.HolderConjugate q)
    (hp : p ≤ 4) : 2/(q-1) ≤ (4 : ℝ)^q := by
  have hq : (4/3 : ℝ) ≤ q := by
    nlinarith [hc.mul_eq_add,mul_le_mul_of_nonneg_right hp hc.symm.sub_one_pos.le]
  have hsix : (6 : ℝ) ≤ (4 : ℝ)^(4/3 : ℝ) := by
    apply (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 3)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [Real.rpow_natCast]
  calc
    2/(q-1) ≤ 6 := (div_le_iff₀ hc.symm.sub_one_pos).mpr (by linarith)
    _ ≤ (4 : ℝ)^(4/3 : ℝ) := hsix
    _ ≤ (4 : ℝ)^q := Real.rpow_le_rpow_of_exponent_le (by norm_num) hq

/-- A constant-eight height coefficient for every conjugate exponent with p<=4. -/
theorem norm_reciprocal_le_eight {p h : ℝ} (hc : p.HolderConjugate q.toReal)
    (hp : p ≤ 4) (hh : 0 < h) (a : Coeff q) (ha0 : ‖a 0‖ ≤ h⁻¹)
    (ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2/(h+|(k : ℝ)|)) :
    ‖a‖ ≤ 8/h^(1/p)+h⁻¹ := by
  simpa only [show (2 : ℝ)*4 = 8 by norm_num] using
    norm_reciprocal_le_of_power_bound hc hh 4 (by norm_num)
      (reciprocal_power_coefficient_le_four hc hp) a ha0 ha

/-- This constant-four power-sum test already fails at p=5 (q=5/4).
This is a limitation of this envelope estimate, not a spectral counterexample. -/
theorem reciprocal_power_coefficient_four_fails_at_five :
    (4 : ℝ)^(5/4 : ℝ) < 2/((5/4 : ℝ)-1) := by
  norm_num
  apply (Real.rpow_lt_rpow_iff (by positivity) (by norm_num) (by norm_num : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [Real.rpow_ofNat]

end NLS.Coeff
