import NLS.ZakharovShabat.HeightResolvent
import NLS.SequenceSpaces.RefinedReciprocalNorm

/-! # Refined free-resolvent height estimates

Keep the exact conjugate-power coefficient. The uniform constant eight
then holds through exponent four, including the endpoints one and four.
-/
noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A reciprocal power-sum coefficient controls the scalar free resolvent. -/
theorem scalarFreeL1Bound_le_height_of_power_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (C : ℝ) (hC : 0 ≤ C) (hcoeff : 2/(p.conjExponent.toReal-1) ≤ C^p.conjExponent.toReal)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    scalarFreeL1Bound p hp z hz ≤ 2*C/|z.im|^(1/p.toReal)+|z.im|⁻¹ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  obtain ⟨n,hn⟩ := exists_centered_real_part z
  let a : Coeff p.conjExponent := Coeff.reindex (Equiv.addRight n) (conjugateInverseSymbol p hp z hz)
  have ha0 : ‖a 0‖ ≤ |z.im|⁻¹ := by
    change ‖(z-(Real.pi : ℂ)*(0+n : ℤ))⁻¹‖ ≤ _
    rw [norm_inv]
    apply inv_anti₀ (abs_pos.mpr him)
    simpa using Complex.abs_im_le_norm (z-(Real.pi : ℂ)*(0+n : ℤ))
  have ha : ∀ k : ℤ, k ≠ 0 → ‖a k‖ ≤ 2/(|z.im|+|(k : ℝ)|) := by
    intro k hk
    change ‖(z-(Real.pi : ℂ)*(k+n : ℤ))⁻¹‖ ≤ _
    simpa only [add_sub_cancel_right] using
      (centered_inverse_height_bound (m := k+n) him hn (by omega))
  have h := Coeff.norm_reciprocal_le_of_power_bound hpq (abs_pos.mpr him) C hC hcoeff a ha0 ha
  change ‖Coeff.reindex (Equiv.addRight n) (conjugateInverseSymbol p hp z hz)‖ ≤ _ at h
  rwa [Coeff.norm_reindex] at h

/-- The same refined coefficient controls both free-resolvent components. -/
theorem freeL1Bound_le_height_of_power_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (C : ℝ) (hC : 0 ≤ C) (hcoeff : 2/(p.conjExponent.toReal-1) ≤ C^p.conjExponent.toReal)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    freeL1Bound p hp z hz ≤ 2*C/|z.im|^(1/p.toReal)+|z.im|⁻¹ := by
  apply max_le
  · simpa only [neg_im,abs_neg] using scalarFreeL1Bound_le_height_of_power_bound hp hp1 C hC hcoeff
      (-z) (neg_notMem_freeLattice hz) (by simpa using him)
  · exact scalarFreeL1Bound_le_height_of_power_bound hp hp1 C hC hcoeff z hz him

/-- A constant-eight resolvent estimate throughout 1<=p<=4. -/
theorem freeL1Bound_le_height_eight (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (z : ℂ) (hz : z ∉ freeLattice) (him : z.im ≠ 0) :
    freeL1Bound p hp z hz ≤ 8/|z.im|^(1/p.toReal)+|z.im|⁻¹ := by
  by_cases hp1 : p = 1
  · subst p
    have h := freeL1Bound_le_height (by simp : (1 : ℝ≥0∞) ≠ ⊤) z hz him
    norm_num only [ENNReal.toReal_one,mul_one,div_one,Real.rpow_one] at h ⊢
    exact h.trans (by have := inv_nonneg.mpr (abs_nonneg z.im); rw [div_eq_mul_inv,div_eq_mul_inv]; linarith)
  · have hp1' : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hp1)
    have hq : p.conjExponent ≠ ⊤ := ne_of_lt
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1')
    have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    have hpr4 : p.toReal ≤ 4 := by exact_mod_cast ENNReal.toReal_mono (by simp) hp4
    simpa only [show (2 : ℝ)*4 = 8 by norm_num] using
      freeL1Bound_le_height_of_power_bound hp hp1' 4 (by norm_num)
        (Coeff.reciprocal_power_coefficient_le_four hc hpr4) z hz him

end NLS.ZakharovShabat
