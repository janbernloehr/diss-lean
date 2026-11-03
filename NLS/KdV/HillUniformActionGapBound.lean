import NLS.KdV.HillCriticalProductBounds
import NLS.KdV.HillWeightedCriticalTail
import NLS.KdV.HillWeightedActionContinuity

/-! # Uniform period-one action-gap and weighted action-tail bounds. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillPeriodOneAction_uniform_gap_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (K n : ℕ) (hK : 2≤K) (hn : K<n)
    (Q r : ℝ) (hQ : 1≤Q) (hqQ : ‖q‖≤Q) (hr0 : 0≤r) (hr1 : r≤1/2)
    (hcut : 8*Q^(3/2-r) ≤ (K : ℝ))
    (hw : ∀ m : ℕ, 1≤m → (m : ℝ)^r ≤ w (2*(m : ℤ))) :
    (n : ℝ)*hillPeriodOneAction w q hr n ≤
      ((K : ℝ)+1)*Real.exp 1*hillPeriodOneGap w q hr n^2 := by
  have hQpow : Q≤Q^(3/2-r) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ (by linarith : 1≤3/2-r)
  have hraw : 8*‖hillPeriodOneUnitPotential w q‖≤(K : ℝ) := by
    linarith [norm_hillPeriodOneUnitPotential_le w q]
  obtain ⟨hs,ht⟩ := hillPeriodOne_critical_log_tail_le_one w q hr (K+1) n (by omega) (by omega)
    Q r hQ hqQ hr0 hr1 (hcut.trans (by exact_mod_cast (show K≤K+1 by omega)))
    (fun k => (Real.rpow_le_rpow (by positivity : 0≤((K+1 : ℕ) : ℝ))
      (by exact_mod_cast (show K+1≤k+(K+1) by omega)) hr0).trans (hw (k+(K+1)) (by omega)))
  have h := hillRealGapIntegral_le_exp_tail (hillPeriodOneUnitPotential w q)
    (hillPeriodOneUnitPotential_even w q) (hillPeriodOneUnitPotential_real w q hr) n K hK hn hraw
    (by simpa only [hillPeriodOneGap,hillPeriodOneLabels,Nat.add_assoc] using hs)
  have ht' : (∑' k : ℕ,
      (hillRealLabels (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
        (hillPeriodOneUnitPotential_real w q hr) (2*(k+K+1))-
       hillRealLabels (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
        (hillPeriodOneUnitPotential_real w q hr) (2*(k+K+1)-1))/
        (4*|((k+K+1 : ℕ) : ℝ)^2-(n : ℝ)^2|)) ≤ 1 := by
    simpa only [hillPeriodOneGap,hillPeriodOneLabels,Nat.add_assoc] using ht
  change (n : ℝ)*hillPeriodOneAction w q hr n ≤
    ((K : ℝ)+1)*Real.exp _*hillPeriodOneGap w q hr n^2 at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht') (by positivity)) (sq_nonneg _))

theorem hillWeightedActionTail_uniform_bound (w : SpectralWeight)
    (p : RealHillWeightedPotential w) (K : ℕ) (hK : 2≤K)
    (Q r : ℝ) (hQ : 1≤Q) (hqQ : ‖p.val‖≤Q) (hr0 : 0≤r) (hr1 : r≤1/2)
    (hcut : 8*Q^(3/2-r) ≤ (K : ℝ))
    (hw : ∀ m : ℕ, 1≤m → (m : ℝ)^r ≤ w (2*(m : ℤ))) :
    (∑' k : ℕ, hillWeightedActionTerm w p (k+K+1)) ≤
      (2*Real.pi)*((K : ℝ)+1)*Real.exp 1*
        (9*‖Coeff.fourierTail (K+1) (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p.val)‖^2+
          2304*‖p.val‖^4/((K : ℝ)+1)) := by
  have hQpow : Q≤Q^(3/2-r) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ (by linarith : 1≤3/2-r)
  have hraw : 8*‖p.val‖≤((K+1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨hgs,hgt⟩ := hillPeriodOne_canonical_gap_tail_bound w p.val p.property (K+1) (by omega) hraw
  have hs : Summable (fun k : ℕ => hillWeightedActionTerm w p (k+K+1)) := by
    have hh := (summable_hillWeightedActionTerm w p).comp_injective
      (i := fun k : ℕ => k+K+1) (by intro a b h; dsimp only at h; omega)
    simpa only [Function.comp_def] using hh
  let C : ℝ := (2*Real.pi)*((K : ℝ)+1)*Real.exp 1
  have hp (k : ℕ) : hillWeightedActionTerm w p (k+K+1) ≤
      C*(w (2*((k+(K+1) : ℕ) : ℤ)))^2*hillPeriodOneGap w p.val p.property (k+(K+1))^2 := by
    have hh := hillPeriodOneAction_uniform_gap_bound w p.val p.property K (k+K+1)
      hK (by omega) Q r hQ hqQ hr0 hr1 hcut hw
    have hmul := mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity : 0≤2*Real.pi)
      (sq_nonneg (w (2*((k+K+1 : ℕ) : ℤ)))))
    convert! hmul using 1 <;> dsimp only [hillWeightedActionTerm,C] <;> rw [Nat.add_assoc] <;> ring
  have hbound := hs.tsum_le_tsum hp (by
    simpa only [mul_assoc] using hgs.mul_left C)
  have he : (∑' k : ℕ, C*(w (2*((k+(K+1) : ℕ) : ℤ)))^2*hillPeriodOneGap w p.val p.property (k+(K+1))^2) =
      C*∑' k : ℕ, (w (2*((k+(K+1) : ℕ) : ℤ)))^2*hillPeriodOneGap w p.val p.property (k+(K+1))^2 := by
    simp only [mul_assoc,tsum_mul_left]
  rw [he] at hbound
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hgt (by dsimp only [C]; positivity))
  simpa only [C,Nat.cast_add,Nat.cast_one] using hh
end NLS.KdV
