import NLS.SequenceSpaces.HillMixedKernel

/-! Sharp logarithmic summability of the unweighted Hill reciprocal kernel.
A variable power estimate is optimized at a=1-1/log(n), so no divergent
harmonic lattice is used as an infinite majorant. -/
noncomputable section
open Set
namespace NLS.ReciprocalSeries

/-- A free power parameter gives arbitrarily close to one full power of
max-distance decay while keeping both translated lattices summable. -/
theorem reciprocal_product_le_max_power (a N u v : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hmax : N ≤ max u v) :
    u⁻¹*v⁻¹ ≤ N^(-a) * (u^(-(2-a))+v^(-(2-a))) := by
  have haux (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) (hNv : N ≤ v) :
      u⁻¹*v⁻¹ ≤ N^(-a)*u^(-(2-a)) := by
    have h1 : v^(-a) ≤ N^(-a) := Real.rpow_le_rpow_of_nonpos hN hNv (by linarith)
    have h2 : v^(a-1) ≤ u^(a-1) := Real.rpow_le_rpow_of_nonpos hu huv (by linarith)
    calc
      _ = v^(-a)*(u^(-1:ℝ)*v^(a-1)) := by
        rw [mul_left_comm,← Real.rpow_add hv]
        simp only [show -a+(a-1) = (-1:ℝ) by ring,Real.rpow_neg_one]
      _ ≤ N^(-a)*(u^(-1:ℝ)*u^(a-1)) :=
        mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hu,show (-1:ℝ)+(a-1)=-(2-a) by ring]
  rcases le_total u v with h | h
  · exact (haux u v hu hv h (by simpa only [max_eq_right h] using hmax)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have ht := haux v u hv hu h (by simpa only [max_eq_left h] using hmax)
    rw [mul_comm v⁻¹ u⁻¹] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (by positivity)) (by positivity))

/-- Pointwise power majorant for the actual unweighted two-resonance kernel. -/
theorem hillKernel_one_le_power (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    mixedHillKernel 1 n k ≤ (n:ℝ)^(-a) *
      (puncturedPower (2-a) ((n:ℤ)+k)+puncturedPower (2-a) ((n:ℤ)-k)) := by
  by_cases hk : k=(n:ℤ) ∨ k=-(n:ℤ)
  · simp only [mixedHillKernel,if_pos hk]
    unfold puncturedPower
    positivity
  have hp : (n:ℤ)+k ≠ 0 := by omega
  have hm : (n:ℤ)-k ≠ 0 := by omega
  have hup : 0 < |(n:ℝ)+(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hp)
  have hum : 0 < |(n:ℝ)-(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hmax : (n:ℝ) ≤ max |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)| := by
    have ht := abs_add_le ((n:ℝ)+(k:ℝ)) ((n:ℝ)-(k:ℝ))
    rw [show (n:ℝ)+(k:ℝ)+((n:ℝ)-(k:ℝ))=2*n by ring,abs_of_nonneg (by positivity)] at ht
    linarith [le_max_left |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|,
      le_max_right |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|]
  simpa only [mixedHillKernel,if_neg hk,puncturedPower,if_neg hp,if_neg hm,
    Int.cast_add,Int.cast_sub,Int.cast_natCast,Real.rpow_neg_one] using
    reciprocal_product_le_max_power a n _ _ ha ha1 (by exact_mod_cast hn) hup hum hmax

/-- The variable-power sum has an explicit constant before optimization. -/
theorem tsum_hillKernel_one_le_power (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑' k : ℤ, mixedHillKernel 1 n k) ≤
      (4*(2-a)/(1-a))*(n:ℝ)^(-a) := by
  let b := 2-a
  have hb : 1 < b := by dsimp [b];linarith
  have hs : Summable (puncturedPower b) := by
    unfold puncturedPower
    simpa only [zero_add] using summable_int_shifted_rpow (α:=0) (by norm_num) hb
  have hp : Summable (fun k : ℤ => puncturedPower b ((n:ℤ)+k)) :=
    hs.comp_injective (Equiv.addLeft (n:ℤ)).injective
  have hm : Summable (fun k : ℤ => puncturedPower b ((n:ℤ)-k)) :=
    hs.comp_injective (Equiv.subLeft (n:ℤ)).injective
  have hbound : (∑' k : ℤ, puncturedPower b k) ≤ 2*(b/(b-1)) := by
    simpa only [puncturedPower,zero_add,add_zero,Real.one_rpow,mul_one] using
      tsum_int_shifted_rpow_le (α:=0) (by norm_num) hb
  calc
    _ ≤ ∑' k : ℤ, (n:ℝ)^(-a)*(puncturedPower b ((n:ℤ)+k)+puncturedPower b ((n:ℤ)-k)) :=
      (summable_mixedHillKernel 1 (by norm_num) le_rfl n hn).tsum_le_tsum
        (hillKernel_one_le_power a ha ha1.le n hn) ((hp.add hm).mul_left _)
    _ = (n:ℝ)^(-a)*(2*∑' k : ℤ, puncturedPower b k) := by
      have hps : (∑' k : ℤ, puncturedPower b ((n:ℤ)+k)) = ∑' k : ℤ, puncturedPower b k :=
        (Equiv.addLeft (n:ℤ)).tsum_eq (puncturedPower b)
      have hms : (∑' k : ℤ, puncturedPower b ((n:ℤ)-k)) = ∑' k : ℤ, puncturedPower b k :=
        (Equiv.subLeft (n:ℤ)).tsum_eq (puncturedPower b)
      rw [tsum_mul_left,hp.tsum_add hm,hps,hms]
      ring
    _ ≤ (n:ℝ)^(-a)*(2*(2*(b/(b-1)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by norm_num)) (by positivity)
    _ = _ := by dsimp [b];rw [show 2-a-1=1-a by ring];ring

/-- Optimizing the power gives the actual logarithmic bound needed by the
periodic half-resolvent, with an absolute explicit constant. -/
theorem tsum_hillKernel_one_le_log (n : ℕ) (hn : 1 ≤ n) (hlog : 1 < Real.log (n:ℝ)) :
    (∑' k : ℤ, mixedHillKernel 1 n k) ≤
      (8*Real.exp 1)*Real.log (n:ℝ)/(n:ℝ) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast hn
  have hlp : 0 < Real.log (n:ℝ) := by linarith
  let a := 1-1/Real.log (n:ℝ)
  have ha : 0 ≤ a := by dsimp [a];have := (div_lt_one hlp).mpr hlog;linarith
  have ha1 : a < 1 := by dsimp [a];have := one_div_pos.mpr hlp;linarith
  have hex : (n:ℝ)^(-a) = Real.exp 1/(n:ℝ) := by
    rw [Real.rpow_def_of_pos hnp]
    have he : Real.log (n:ℝ)*(-a) = 1-Real.log (n:ℝ) := by
      dsimp [a];field_simp [hlp.ne'];ring
    rw [he,Real.exp_sub,Real.exp_log hnp]
  have hec : 4*(2-a)/(1-a) = 4*(Real.log (n:ℝ)+1) := by
    dsimp [a];field_simp [hlp.ne'];ring
  have hs := tsum_hillKernel_one_le_power a ha ha1 n hn
  rw [hex,hec] at hs
  apply hs.trans
  have hfac : 0 ≤ Real.exp 1/(n:ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right (show 4*(Real.log (n:ℝ)+1) ≤ 8*Real.log (n:ℝ) by linarith) hfac
  convert h using 1; ring

end NLS.ReciprocalSeries
