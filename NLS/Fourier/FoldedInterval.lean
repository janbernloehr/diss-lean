import NLS.Fourier.IntervalKernel

/-!
# Fourier coefficients of a reflected interval

On `[0,2]`, retain `f` on the first half and use a scalar multiple of the
reflection of `g` on the second half. The normalized period-two Fourier
coefficient is derived by splitting and changing variables in the integral.
This allows a jump at the gluing point; its value does not affect the coefficient.
-/

noncomputable section
open Complex MeasureTheory Set
namespace NLS.Fourier

/-- A reflected block on `[0,2]`; only values on that interval enter the Fourier coefficient. -/
def folded (ε : ℂ) (f g : ℝ → ℂ) (x : ℝ) : ℂ := if x ≤ 1 then f x else ε * g (2 - x)

/-- The normalized Fourier coefficient of a function on one period of length two. -/
def periodTwoCoefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..2, f x * wave (-n) x

/-- The contribution to that coefficient from the original unit interval. -/
def halfCoefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (1 / 2 : ℂ) * ∫ x in (0 : ℝ)..1, f x * wave (-n) x

private theorem folded_first (ε : ℂ) (f g : ℝ → ℂ) (n : ℤ) :
    EqOn (fun x => folded ε f g x * wave (-n) x)
      (fun x => f x * wave (-n) x) (uIoc (0 : ℝ) 1) := by
  intro x hx
  have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
  simp [folded, hx']

private theorem folded_second (ε : ℂ) (f g : ℝ → ℂ) (n : ℤ) :
    EqOn (fun x => folded ε f g x * wave (-n) x)
      (fun x => ε * g (2 - x) * wave (-n) x) (uIoc (1 : ℝ) 2) := by
  intro x hx
  have hx' : 1 < x := (show x ∈ Ioc (1 : ℝ) 2 from by simpa using hx).1
  simp [folded, not_le.mpr hx']

/-- Splitting the physical integral gives exactly the half-coefficient reflection formula. -/
theorem periodTwoCoefficient_folded (ε : ℂ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    periodTwoCoefficient (folded ε f g) n = halfCoefficient f n + ε * halfCoefficient g (-n) := by
  have hleft : IntervalIntegrable (fun x => f x * wave (-n) x) volume 0 1 :=
    (hf.mul (continuous_wave (-n))).intervalIntegrable 0 1
  have hright : Continuous (fun x : ℝ => ε * g (2 - x) * wave (-n) x) := by fun_prop
  have h01 : IntervalIntegrable (fun x => folded ε f g x * wave (-n) x) volume 0 1 :=
    hleft.congr (folded_first ε f g n).symm
  have h12 : IntervalIntegrable (fun x => folded ε f g x * wave (-n) x) volume 1 2 :=
    (hright.intervalIntegrable 1 2).congr (folded_second ε f g n).symm
  have he01 : (∫ x in (0 : ℝ)..1, folded ε f g x * wave (-n) x) =
      ∫ x in (0 : ℝ)..1, f x * wave (-n) x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (folded_first ε f g n))
  have he12 : (∫ x in (1 : ℝ)..2, folded ε f g x * wave (-n) x) =
      ∫ x in (1 : ℝ)..2, ε * g (2 - x) * wave (-n) x :=
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (folded_second ε f g n))
  have href : (∫ x in (1 : ℝ)..2, ε * g (2 - x) * wave (-n) x) =
      ε * ∫ x in (0 : ℝ)..1, g x * wave n x := by
    have he : (fun x : ℝ => ε * g (2 - x) * wave (-n) x) =
        (fun x : ℝ => ε * (g (2 - x) * wave n (2 - x))) := by
      funext x
      rw [wave_reflect]
      ring
    rw [he, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => g x * wave n x) 2]
    norm_num
  unfold periodTwoCoefficient halfCoefficient
  rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12, he01, he12, href, neg_neg]
  ring

/-- Finite period-one Fourier synthesis in the raw frequency convention. -/
def polynomial (a : ℤ →₀ ℂ) (x : ℝ) : ℂ := a.sum (fun k z => z * wave (2 * k) x)

theorem continuous_polynomial (a : ℤ →₀ ℂ) : Continuous (polynomial a) := by
  unfold polynomial Finsupp.sum
  fun_prop

/-- The physical overlap integral computes every coefficient of a finite Fourier polynomial. -/
theorem halfCoefficient_polynomial (a : ℤ →₀ ℂ) (n : ℤ) :
    halfCoefficient (polynomial a) n = a.sum (fun k z => z * overlap k n) := by
  unfold halfCoefficient polynomial Finsupp.sum
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have he : (fun x : ℝ => a k * wave (2 * k) x * wave (-n) x) =
        (fun x : ℝ => a k * (wave (2 * k) x * wave (-n) x)) := by funext x; ring
    rw [he, intervalIntegral.integral_const_mul]
    unfold overlap
    ring
  · intro k hk
    exact ((continuous_const.mul (continuous_wave (2 * k))).mul
      (continuous_wave (-n))).intervalIntegrable 0 1

/-- Even output indices retain the corresponding input coefficient, with the normalization `1/2`. -/
theorem halfCoefficient_polynomial_even (a : ℤ →₀ ℂ) (l : ℤ) :
    halfCoefficient (polynomial a) (2 * l) = (1 / 2 : ℂ) * a l := by
  classical
  rw [halfCoefficient_polynomial]
  simp only [Finsupp.sum, overlap_even, mul_ite, mul_zero]
  simp [Finsupp.mem_support_iff, mul_comm]

/-- Odd output indices give the exact shifted reciprocal sum. -/
theorem halfCoefficient_polynomial_odd (a : ℤ →₀ ℂ) (l : ℤ) :
    halfCoefficient (polynomial a) (2 * l + 1) =
      a.sum (fun k z => z * (I / ((Real.pi : ℂ) * (2 * k - 2 * l - 1)))) := by
  rw [halfCoefficient_polynomial]
  simp only [overlap_odd]

end NLS.Fourier
