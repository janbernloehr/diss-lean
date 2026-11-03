import NLS.SequenceSpaces.ReciprocalSeries
import NLS.SequenceSpaces.NonnegativeSeriesCauchySchwarz
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Summable reciprocal quadratic spectral separation and its Cauchy–Schwarz bound. -/

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SequenceSpaces

theorem reciprocal_square_separation_bound (m n N : ℕ) (hN : 1 ≤ N)
    (hm : N ≤ m) (hn : N ≤ n) :
    1 / |(m : ℝ)^2-(n : ℝ)^2|^2 ≤
      (1/(4*(N : ℝ)^2)) * (if m=n then 0 else 1/|(m : ℝ)-(n : ℝ)|^2) := by
  by_cases he : m=n
  · subst m
    simp
  · rw [if_neg he]
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0<N by omega)
    have hmr : (N : ℝ) ≤ m := by exact_mod_cast hm
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hd : 0 < |(m : ℝ)-(n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast he))
    have heq : |(m : ℝ)^2-(n : ℝ)^2| = |(m : ℝ)-(n : ℝ)| *((m : ℝ)+n) := by
      rw [sq_sub_sq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)+n)]
      ring
    rw [heq]
    have hden : |(m : ℝ)-(n : ℝ)|^2*(4*(N : ℝ)^2) ≤
        (|(m : ℝ)-(n : ℝ)| *((m : ℝ)+n))^2 := by
      have hs : (2*(N : ℝ))^2 ≤ ((m : ℝ)+n)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg |(m : ℝ)-(n : ℝ)|)]
    calc
      _ ≤ 1/(|(m : ℝ)-(n : ℝ)|^2*(4*(N : ℝ)^2)) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
      _ = _ := by ring

theorem summable_quadratic_separation_tail (N n : ℕ) (hN : 1 ≤ N) (hn : N ≤ n) :
    Summable (fun k : ℕ => 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|^2) ∧
      (∑' k : ℕ, 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|^2) ≤ 1/(N : ℝ)^2 := by
  let f : ℤ → ℝ := fun j => if j=(n : ℤ) then 0 else 1/|((j-(n : ℤ) : ℤ) : ℝ)|^2
  have hf : Summable f := by
    have hs := NLS.ReciprocalSeries.summable_int_shifted_rpow (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (1 : ℝ)<2)
    have ht := hs.comp_injective (i := fun j : ℤ => j-(n : ℤ)) (by intro a b h; dsimp only at h; omega)
    convert! ht using 1
    funext j
    simp only [f,Function.comp_def,sub_eq_zero,zero_add,Real.rpow_neg (abs_nonneg _),Real.rpow_two,one_div]
  have hf0 (j : ℤ) : 0 ≤ f j := by dsimp only [f]; split_ifs <;> positivity
  have hfbound : (∑' j : ℤ, f j) ≤ 4 := by
    have hh := NLS.ReciprocalSeries.tsum_int_centered_shifted_rpow_le (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (1 : ℝ)<2) (n : ℤ)
    convert! hh using 1
    · simp only [f,zero_add,Real.rpow_neg (abs_nonneg _),Real.rpow_two,one_div]
    · norm_num
  let i : ℕ → ℤ := fun k => ((k+N : ℕ) : ℤ)
  have hi : Function.Injective i := by intro a b h; dsimp only [i] at h; omega
  have he (k : ℕ) : f (i k) = if k+N=n then 0 else 1/|((k+N : ℕ) : ℝ)-(n : ℝ)|^2 := by
    simp only [f,i,Int.cast_sub,Int.cast_natCast,Nat.cast_inj]
  have hs := (hf.comp_injective hi).mul_left (1/(4*(N : ℝ)^2))
  have hb (k : ℕ) : 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|^2 ≤
      (1/(4*(N : ℝ)^2))*f (i k) := by
    rw [he]
    exact reciprocal_square_separation_bound (k+N) n N hN (by omega) hn
  have hsum := Summable.of_nonneg_of_le (fun k : ℕ => by positivity : ∀ k : ℕ, 0 ≤ 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|^2) hb hs
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' k : ℕ, (1/(4*(N : ℝ)^2))*f (i k) := hsum.tsum_le_tsum hb hs
    _ = (1/(4*(N : ℝ)^2)) * ∑' k : ℕ, f (i k) := tsum_mul_left
    _ ≤ (1/(4*(N : ℝ)^2)) * ∑' j : ℤ, f j :=
      mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hf hf0 hi) (by positivity)
    _ ≤ (1/(4*(N : ℝ)^2))*4 := mul_le_mul_of_nonneg_left hfbound (by positivity)
    _ = _ := by ring

theorem quadratic_separation_cauchy_schwarz (g : ℕ → ℝ) (N n : ℕ)
    (hN : 1 ≤ N) (hn : N ≤ n) (hg : ∀ k, 0 ≤ g k)
    (hs : Summable (fun k => (g k)^2)) :
    Summable (fun k : ℕ => g k/(4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|)) ∧
      (∑' k : ℕ, g k/(4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|))^2 ≤
        (∑' k, (g k)^2)/(16*(N : ℝ)^2) := by
  let b : ℕ → ℝ := fun k => 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|
  obtain ⟨hbs,hbt⟩ := summable_quadratic_separation_tail N n hN hn
  have he (k : ℕ) : (b k)^2 = 1/|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|^2 := by
    dsimp only [b]
    rw [one_div_pow]
  have hbs' : Summable (fun k => (b k)^2) := by simpa only [he] using hbs
  obtain ⟨hcs,hc⟩ := nonneg_series_cauchy_schwarz g b hg (fun k => by dsimp only [b]; positivity) hs hbs'
  have hterm (k : ℕ) : g k/(4*|((k+N : ℕ) : ℝ)^2-(n : ℝ)^2|) = (g k*b k)/4 := by
    dsimp only [b]
    ring
  simp_rw [hterm]
  refine ⟨hcs.div_const 4,?_⟩
  rw [tsum_div_const]
  have hA : 0 ≤ ∑' k, (g k)^2 := tsum_nonneg (fun k => sq_nonneg _)
  have hcb := hc.trans (mul_le_mul_of_nonneg_left (by simpa only [he] using hbt) hA)
  calc
    _ = (∑' k, g k*b k)^2/16 := by ring
    _ ≤ ((∑' k, (g k)^2)*(1/(N : ℝ)^2))/16 := div_le_div_of_nonneg_right hcb (by norm_num)
    _ = _ := by ring


end NLS.SequenceSpaces
