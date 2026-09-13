import NLS.ZakharovShabat.FreeMultiplicity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

/-!
# Symmetric free spectral products

The doubled free eigenvalues are `π n`, with algebraic multiplicity two.
Pairing opposite indices gives the symmetric products used in Chapter 2.
Euler's product fixes their normalization, including the exceptional zero mode.
-/

noncomputable section
open Filter Topology
namespace NLS.ZakharovShabat

/-- The doubled free spectral factor, with denominator one at the zero mode. -/
def freeSpectralFactor (h z : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then z^2 else ((h*n-z)/(h*n))^2

@[simp] theorem freeSpectralFactor_zero (h z : ℂ) : freeSpectralFactor h z 0 = z^2 := by
  simp [freeSpectralFactor]

/-- Rescaling the lattice by two selects the actual even free spectral values. -/
theorem freeSpectralFactor_even (h z : ℂ) (n : ℤ) :
    freeSpectralFactor (2*h) z n = freeSpectralFactor h z (2*n) := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [freeSpectralFactor, if_neg hn, freeSpectralFactor, if_neg (by omega)]
    have he : h*((2*n : ℤ) : ℂ) = (2*h)*n := by push_cast; ring
    rw [he]

/-- Symmetric partial products: the zero mode followed by both signs of each positive mode. -/
def freeSpectralPartialProduct (h z : ℂ) (N : ℕ) : ℂ :=
  freeSpectralFactor h z 0 * ∏ j ∈ Finset.range N,
    (freeSpectralFactor h z ((j : ℤ)+1) * freeSpectralFactor h z (-((j : ℤ)+1)))

/-- Symmetric integer cutoffs contain exactly the zero mode and both signs of each positive mode. -/
theorem prod_symmetric_interval (f : ℤ → ℂ) (N : ℕ) :
    (∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n) =
      f 0 * ∏ j ∈ Finset.range N, (f ((j : ℤ)+1) * f (-((j : ℤ)+1))) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : Finset.Icc (-(↑(N+1) : ℤ)) (↑(N+1) : ℤ) =
        insert (-(↑(N+1) : ℤ)) (insert (↑(N+1) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hleft : -(↑(N+1) : ℤ) ∉ insert (↑(N+1) : ℤ) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have hright : (↑(N+1) : ℤ) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hs, Finset.prod_insert hleft, Finset.prod_insert hright, ih, Finset.prod_range_succ]
    push_cast
    ring

/-- The paired definition is the literal symmetric integer-cutoff product. -/
theorem freeSpectralPartialProduct_eq_prod_Icc (h z : ℂ) (N : ℕ) :
    freeSpectralPartialProduct h z N = ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), freeSpectralFactor h z n :=
  (prod_symmetric_interval (freeSpectralFactor h z) N).symm

/-- Opposite lattice modes cancel the nonsummable linear term. -/
theorem freeSpectralFactor_pair (h z : ℂ) (hh : h ≠ 0) (j : ℕ) :
    freeSpectralFactor h z ((j : ℤ)+1) * freeSpectralFactor h z (-((j : ℤ)+1)) =
      (1-z^2/(h*((j : ℂ)+1))^2)^2 := by
  rw [freeSpectralFactor, if_neg (by omega), freeSpectralFactor, if_neg (by omega)]
  push_cast
  have hj : (j : ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero j
  field_simp
  ring

/-- The actual symmetric factors equal the square of Euler's normalized positive-mode product. -/
theorem freeSpectralPartialProduct_eq (h z : ℂ) (hh : h ≠ 0) (N : ℕ) :
    freeSpectralPartialProduct h z N =
      (z * ∏ j ∈ Finset.range N, (1-z^2/(h*((j : ℂ)+1))^2))^2 := by
  simp only [freeSpectralPartialProduct, freeSpectralFactor_zero, freeSpectralFactor_pair h z hh]
  rw [Finset.prod_pow, mul_pow]

/-- Symmetric products converge for every complex parameter, including all free eigenvalues. -/
theorem tendsto_freeSpectralPartialProduct (h z : ℂ) (hh : h ≠ 0) :
    Tendsto (freeSpectralPartialProduct h z) atTop
      (𝓝 ((h/(Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ)*z/h))^2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he := ((Complex.tendsto_euler_sin_prod (z/h)).const_mul (h/(Real.pi : ℂ))).pow 2
  convert he using 1
  · funext N
    rw [freeSpectralPartialProduct_eq h z hh]
    congr 1
    have hc : h/(Real.pi : ℂ) * ((Real.pi : ℂ)*(z/h)) = z := by field_simp
    rw [← mul_assoc, hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    rw [div_pow, mul_pow, div_div]
  · simp only [mul_div_assoc]

/-- The free discriminant in the period-one convention. -/
def freeDiscriminant (z : ℂ) : ℂ := 2 * Complex.cos z

/-- Equation (2.1) has the correct free normalization `-4`. -/
theorem tendsto_freePeriodicFullProduct (z : ℂ) :
    Tendsto (fun N => -4 * freeSpectralPartialProduct (Real.pi : ℂ) z N) atTop
      (𝓝 ((freeDiscriminant z)^2-4)) := by
  have h := (tendsto_freeSpectralPartialProduct (Real.pi : ℂ) z
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).const_mul (-4)
  have hz : (Real.pi : ℂ) * z / (Real.pi : ℂ) = z :=
    mul_div_cancel_left₀ z (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have ht : -4 * Complex.sin z ^ 2 = (freeDiscriminant z)^2-4 := by
    have hs := Complex.sin_sq_add_cos_sq z
    unfold freeDiscriminant
    linear_combination -4 * hs
  simpa only [div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), one_mul, hz, ht] using h

/-- The period-one subproduct needs prefactor `-1`, as in the proof following Lemma 8.1. -/
theorem tendsto_freePeriodOneProduct (z : ℂ) :
    Tendsto (fun N => -freeSpectralPartialProduct (2*(Real.pi : ℂ)) z N) atTop
      (𝓝 (freeDiscriminant z-2)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (tendsto_freeSpectralPartialProduct (2*(Real.pi : ℂ)) z (mul_ne_zero two_ne_zero hpi)).neg
  have hc : (2*(Real.pi : ℂ))/(Real.pi : ℂ) = 2 := mul_div_cancel_right₀ 2 hpi
  have hz : (Real.pi : ℂ)*z/(2*(Real.pi : ℂ)) = z/2 := by field_simp
  have ht : -(2 * Complex.sin (z/2))^2 = freeDiscriminant z-2 := by
    have hs := Complex.sin_sq_add_cos_sq (z/2)
    have hc := Complex.cos_two_mul (z/2)
    rw [show 2*(z/2) = z by ring] at hc
    unfold freeDiscriminant
    linear_combination -4 * hs - 2 * hc
  simpa only [hc, hz, ht] using h

end NLS.ZakharovShabat
