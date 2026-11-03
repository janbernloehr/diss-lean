import NLS.KdV.HillWeightedActionHead
import NLS.KdV.HillUniformActionGapBound
import NLS.SequenceSpaces.SpectralWeightCeilingCutoff
import NLS.SequenceSpaces.QuadraticCutoffRounding

/-! # The full weighted Hill action estimate at the exact source weight argument. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillWeightedAction_total_cutoff_bound (w : SpectralWeight)
    (p : RealHillWeightedPotential w) (hmean : p.val.val 0=0) (K : ℕ) (hK : 2≤K)
    (Q r : ℝ) (hQ : 1≤Q) (hqQ : ‖p.val‖≤Q) (hr0 : 0≤r) (hr1 : r≤1/2)
    (hcut : 8*Q^(3/2-r) ≤ (K : ℝ))
    (hw : ∀ m : ℕ, 1≤m → (m : ℝ)^r ≤ w (2*(m : ℤ))) :
    (∑' n : ℕ, hillWeightedActionTerm w p n) ≤
      (w (2*(K : ℤ)))^2*((1/2 : ℝ)*‖p.val‖^2)+
      (2*Real.pi)*((K : ℝ)+1)*Real.exp 1*(9*‖p.val‖^2+2304*‖p.val‖^4/((K : ℝ)+1)) := by
  have hhead := hillWeightedAction_head_bound w p hmean K
  have htail := hillWeightedActionTail_uniform_bound w p K hK Q r hQ hqQ hr0 hr1 hcut hw
  have hn := Coeff.norm_fourierTail_le (by norm_num : (2 : ENNReal)≠0) (K+1)
    (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p.val)
  rw [← WeightedCoeff.norm_eq] at hn
  have hns : ‖Coeff.fourierTail (K+1) (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p.val)‖^2≤‖p.val‖^2 := by
    nlinarith [norm_nonneg (Coeff.fourierTail (K+1) (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p.val))]
  have htail' := htail.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hns (by norm_num : (0 : ℝ)≤9)) le_rfl)
    (by positivity : 0≤(2*Real.pi)*((K : ℝ)+1)*Real.exp 1))
  have hsplit := (summable_hillWeightedActionTerm w p).sum_add_tsum_nat_add (K+1)
  rw [← hsplit]
  apply add_le_add hhead
  simpa only [Nat.add_assoc] using htail'

theorem hillWeightedAction_total_norm_bound (w : SpectralWeight) (r : ℝ)
    (hr0 : 0≤r) (hr1 : r≤1/2)
    (hw : ∀ m : ℕ, 1≤m → (m : ℝ)^r ≤ w (2*(m : ℤ)))
    (p : RealHillWeightedPotential w) (hmean : p.val.val 0=0) :
    (∑' n : ℕ, hillWeightedActionTerm w p n) ≤
      (5000*Real.pi*Real.exp 1+(w (16 : ℤ)*w (3 : ℤ))^2)*
        ((1+‖p.val‖)^2+(w.realExtension (16*‖p.val‖^(3/2-r)))^2)*‖p.val‖^2 := by
  let t : ℝ := ‖p.val‖
  let Q : ℝ := max 1 t
  let K : ℕ := ⌈8*Q^(3/2-r)⌉₊
  let W : ℝ := w.realExtension (16*t^(3/2-r))
  let H : ℝ := w (16 : ℤ)*w (3 : ℤ)
  have ht : 0≤t := norm_nonneg _
  have hQ : 1≤Q := le_max_left _ _
  have hpow : 1≤Q^(3/2-r) := Real.one_le_rpow hQ (by linarith)
  have hcut : 8*Q^(3/2-r)≤(K : ℝ) := Nat.le_ceil _
  have hK : 2≤K := by
    have hh : (2 : ℝ)≤K := by linarith
    exact_mod_cast hh
  have htotal := hillWeightedAction_total_cutoff_bound w p hmean K hK Q r hQ
    (le_max_right _ _) hr0 hr1 hcut hw
  have hKbound : (K : ℝ)+1≤10*(1+t)^2 :=
    NLS.SequenceSpaces.ceiling_weighted_cutoff_le_quadratic t r ht hr0
  have hweight : w (2*(K : ℤ))≤H*W := by
    simpa only [K,Q,H,W,Nat.cast_mul,Nat.cast_ofNat] using w.ceiling_cutoff_weight_le t (3/2-r) ht
  have hwsq : (w (2*(K : ℤ)))^2≤H^2*W^2 := by
    have hh := pow_le_pow_left₀ (w.positive _).le hweight 2
    simpa only [mul_pow] using hh
  have hhead : (w (2*(K : ℤ)))^2*((1/2 : ℝ)*t^2)≤H^2*W^2*t^2 := by
    have hh := mul_le_mul_of_nonneg_right hwsq (by positivity : 0≤(1/2 : ℝ)*t^2)
    nlinarith [sq_nonneg (H*W*t)]
  have htail : (2*Real.pi)*((K : ℝ)+1)*Real.exp 1*(9*t^2+2304*t^4/((K : ℝ)+1)) ≤
      5000*Real.pi*Real.exp 1*(1+t)^2*t^2 := by
    have hkpos : 0<(K : ℝ)+1 := by positivity
    have heq : (2*Real.pi)*((K : ℝ)+1)*Real.exp 1*(9*t^2+2304*t^4/((K : ℝ)+1)) =
        18*Real.pi*Real.exp 1*((K : ℝ)+1)*t^2+4608*Real.pi*Real.exp 1*t^4 := by
      field_simp [ne_of_gt hkpos]
      ring
    rw [heq]
    have hfirst := mul_le_mul_of_nonneg_right hKbound (by positivity : 0≤18*Real.pi*Real.exp 1*t^2)
    have ht4 : t^4≤(1+t)^2*t^2 := by nlinarith [mul_nonneg (by linarith : 0≤1+2*t) (sq_nonneg t)]
    have hsecond := mul_le_mul_of_nonneg_left ht4 (by positivity : 0≤4608*Real.pi*Real.exp 1)
    nlinarith [Real.pi_pos,Real.exp_pos (1 : ℝ)]
  change (∑' n : ℕ, hillWeightedActionTerm w p n)≤(5000*Real.pi*Real.exp 1+H^2)*((1+t)^2+W^2)*t^2
  apply htotal.trans
  change (w (2*(K : ℤ)))^2*((1/2 : ℝ)*t^2)+_≤_
  have hsum := add_le_add hhead htail
  apply hsum.trans
  nlinarith [mul_nonneg (by positivity : 0≤5000*Real.pi*Real.exp 1) (sq_nonneg (W*t)),
    mul_nonneg (sq_nonneg H) (sq_nonneg ((1+t)*t))]

end NLS.KdV
