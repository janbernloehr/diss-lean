import NLS.SequenceSpaces.ReciprocalSeries
import Mathlib.Tactic

/-!
# The mixed reciprocal kernel at the pseudomeasure endpoint

For 0<a<=1, the sum of |n+k|^(-a)|n-k|^(-1), omitting k=+-n,
is bounded by (4+8/a)n^(-a/2). With a=1-2|s| this is the exact
n^(-(1/2-|s|)) decay required by the negative-regularity endpoint.
-/
noncomputable section
open Set
namespace NLS.ReciprocalSeries

/-- The scalar maximum-distance estimate underlying the mixed lattice sum. -/
theorem mixed_power_le_max_decay (a N u v : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hN : 0 < N) (hu : 0 < u) (hv : 0 < v) (hmax : N ≤ max u v) :
    u^(-a)*v^(-1:ℝ) ≤ N^(-a/2) *
      (u^(-(1+a/2)) + v^(-(1+a/2))) := by
  have hna : -a/2 ≤ 0 := by linarith
  rcases le_total u v with huv | hvu
  · have hNv : N ≤ v := by simpa only [max_eq_right huv] using hmax
    have h1 : v^(-a/2) ≤ N^(-a/2) := Real.rpow_le_rpow_of_nonpos hN hNv hna
    have hb : -(1-a/2) ≤ 0 := by linarith
    have h2 : v^(-(1-a/2)) ≤ u^(-(1-a/2)) := Real.rpow_le_rpow_of_nonpos hu huv hb
    calc
      _ = v^(-a/2) * (u^(-a)*v^(-(1-a/2))) := by
        rw [mul_left_comm, ← Real.rpow_add hv,
          show -a/2 + -(1-a/2) = (-1:ℝ) by ring]
      _ ≤ N^(-a/2) * (u^(-a)*u^(-(1-a/2))) := by
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hu.le _))
          (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _))
          (Real.rpow_nonneg hN.le _)
      _ = N^(-a/2)*u^(-(1+a/2)) := by
        rw [← Real.rpow_add hu, show -a + -(1-a/2) = -(1+a/2) by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.rpow_nonneg hv.le _)) (Real.rpow_nonneg hN.le _)
  · have hNu : N ≤ u := by simpa only [max_eq_left hvu] using hmax
    have h1 : u^(-a/2) ≤ N^(-a/2) := Real.rpow_le_rpow_of_nonpos hN hNu hna
    have h2 : u^(-a/2) ≤ v^(-a/2) := Real.rpow_le_rpow_of_nonpos hv hvu hna
    calc
      _ = u^(-a/2)*(u^(-a/2)*v^(-1:ℝ)) := by
        rw [← mul_assoc, ← Real.rpow_add hu, show -a/2 + -a/2 = -a by ring]
      _ ≤ N^(-a/2)*(v^(-a/2)*v^(-1:ℝ)) := by
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hv.le _))
          (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _))
          (Real.rpow_nonneg hN.le _)
      _ = N^(-a/2)*v^(-(1+a/2)) := by
        rw [← Real.rpow_add hv, show -a/2 + (-1:ℝ) = -(1+a/2) by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.rpow_nonneg hu.le _)) (Real.rpow_nonneg hN.le _)

/-- Punctured reciprocal powers, with the central value fixed to zero. -/
def puncturedPower (b : ℝ) (k : ℤ) : ℝ := if k=0 then 0 else |(k:ℝ)|^(-b)

/-- The two resonances are excluded from the mixed Hill kernel. -/
def mixedHillKernel (a : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  if k=(n:ℤ) ∨ k=-(n:ℤ) then 0 else
    |(n:ℝ)+(k:ℝ)|^(-a) * |(n:ℝ)-(k:ℝ)|^(-1:ℝ)

theorem mixedHillKernel_nonneg (a : ℝ) (n : ℕ) (k : ℤ) : 0 ≤ mixedHillKernel a n k := by
  unfold mixedHillKernel
  split_ifs <;> positivity

/-- A summable pair of translated power lattices dominates the whole kernel. -/
theorem mixedHillKernel_le (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (n : ℕ) (hn : 1≤n) (k : ℤ) :
    mixedHillKernel a n k ≤ (n:ℝ)^(-a/2) *
      (puncturedPower (1+a/2) ((n:ℤ)+k) + puncturedPower (1+a/2) ((n:ℤ)-k)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  by_cases hk : k=(n:ℤ) ∨ k=-(n:ℤ)
  · simp only [mixedHillKernel, if_pos hk]
    unfold puncturedPower
    positivity
  · have hk1 : k ≠ (n:ℤ) := fun h => hk (Or.inl h)
    have hk2 : k ≠ -(n:ℤ) := fun h => hk (Or.inr h)
    have hplus : (n:ℤ)+k ≠ 0 := by omega
    have hminus : (n:ℤ)-k ≠ 0 := by omega
    have hp : 0 < |(n:ℝ)+(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hplus)
    have hm : 0 < |(n:ℝ)-(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hminus)
    have hmax : (n:ℝ) ≤ max |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)| := by
      have ht := abs_add_le ((n:ℝ)+(k:ℝ)) ((n:ℝ)-(k:ℝ))
      rw [show (n:ℝ)+(k:ℝ)+((n:ℝ)-(k:ℝ)) = 2*n by ring,
        abs_of_nonneg (by positivity : 0≤2*(n:ℝ))] at ht
      have h1 := le_max_left |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|
      have h2 := le_max_right |(n:ℝ)+(k:ℝ)| |(n:ℝ)-(k:ℝ)|
      linarith
    simpa only [mixedHillKernel, if_neg hk, puncturedPower, if_neg hplus,
      if_neg hminus, Int.cast_add, Int.cast_natCast, Int.cast_sub] using
      mixed_power_le_max_decay a n _ _ ha ha1 hn0 hp hm hmax

/-- Full summability, without a finite source-exponent hypothesis. -/
theorem summable_mixedHillKernel (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (n : ℕ) (hn : 1≤n) : Summable (mixedHillKernel a n) := by
  have hs : Summable (puncturedPower (1+a/2)) := by
    unfold puncturedPower
    simpa only [zero_add] using
      summable_int_shifted_rpow (α:=0) (by norm_num) (show 1<1+a/2 by linarith)
  have hplus := hs.comp_injective (Equiv.addLeft (n:ℤ)).injective
  have hminus := hs.comp_injective (Equiv.subLeft (n:ℤ)).injective
  exact ((hplus.add hminus).mul_left ((n:ℝ)^(-a/2))).of_nonneg_of_le
    (mixedHillKernel_nonneg a n) (mixedHillKernel_le a ha ha1 n hn)

/-- Explicit uniform lattice bound for every real endpoint regularity exponent. -/
theorem tsum_mixedHillKernel_le (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (n : ℕ) (hn : 1≤n) :
    (∑' k : ℤ, mixedHillKernel a n k) ≤
      (4+8/a) * (n:ℝ)^(-a/2) := by
  let b := 1+a/2
  have hb : 1<b := by dsimp [b]; linarith
  have hs : Summable (puncturedPower b) := by
    unfold puncturedPower
    simpa only [zero_add] using summable_int_shifted_rpow (α:=0) (by norm_num) hb
  have hp : Summable (fun k : ℤ => puncturedPower b ((n:ℤ)+k)) :=
    hs.comp_injective (Equiv.addLeft (n:ℤ)).injective
  have hm : Summable (fun k : ℤ => puncturedPower b ((n:ℤ)-k)) :=
    hs.comp_injective (Equiv.subLeft (n:ℤ)).injective
  have hbound : (∑' k : ℤ, puncturedPower b k) ≤ 2*(b/(b-1)) := by
    simpa only [puncturedPower, zero_add, add_zero, Real.one_rpow, mul_one] using
      tsum_int_shifted_rpow_le (α:=0) (by norm_num) hb
  calc
    _ ≤ ∑' k : ℤ, (n:ℝ)^(-a/2) *
        (puncturedPower b ((n:ℤ)+k)+puncturedPower b ((n:ℤ)-k)) :=
      (summable_mixedHillKernel a ha ha1 n hn).tsum_le_tsum
        (mixedHillKernel_le a ha ha1 n hn) ((hp.add hm).mul_left _)
    _ = (n:ℝ)^(-a/2) * (2 * ∑' k : ℤ, puncturedPower b k) := by
      have hps : (∑' k : ℤ, puncturedPower b ((n:ℤ)+k)) = ∑' k : ℤ, puncturedPower b k :=
        (Equiv.addLeft (n:ℤ)).tsum_eq (puncturedPower b)
      have hms : (∑' k : ℤ, puncturedPower b ((n:ℤ)-k)) = ∑' k : ℤ, puncturedPower b k :=
        (Equiv.subLeft (n:ℤ)).tsum_eq (puncturedPower b)
      rw [tsum_mul_left, hp.tsum_add hm, hps, hms]
      ring
    _ ≤ (n:ℝ)^(-a/2) * (2 * (2*(b/(b-1)))) := by
      gcongr
    _ = _ := by
      dsimp [b]
      field_simp [ha.ne']
      ring

end NLS.ReciprocalSeries
