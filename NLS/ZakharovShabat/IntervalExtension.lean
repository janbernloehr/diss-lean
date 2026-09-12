import NLS.Fourier.FoldedInterval
import NLS.ZakharovShabat.BoundaryResolvent

/-!
# Physical interval extensions and their Fourier coefficients

The Dirichlet extension retains a pair on `[0,1]` and reflects/swaps it on
`[1,2]`; Neumann inserts a minus sign on the reflected half. These are the
actual piecewise extensions in Chapter 1, §4, not the period-two boundary
projections. The coefficient formulas are proved from the normalized integrals
in (1.8)–(1.9), first for continuous functions and then finite Fourier polynomials.
The uniform `ℓp → ℓp` estimate for `1 < p < ∞` is a separate remaining step.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
open NLS.Fourier

/-- The sign on the reflected half interval. -/
def extensionSign : BoundaryCondition → ℂ
  | .dirichlet => 1
  | .neumann => -1

variable (b : BoundaryCondition)

@[simp] theorem extensionSign_sq : extensionSign b * extensionSign b = 1 := by cases b <;> norm_num [extensionSign]

/-- The physical reflected extension on `[0,2]`, as a linear operation on pairs of functions. -/
def intervalExtension : (ℝ → ℂ × ℂ) →ₗ[ℂ] (ℝ → ℂ × ℂ) where
  toFun f x := (folded (extensionSign b) (fun y => (f y).1) (fun y => (f y).2) x,
    folded (extensionSign b) (fun y => (f y).2) (fun y => (f y).1) x)
  map_add' f g := by
    funext x
    by_cases hx : x ≤ 1 <;> ext <;> simp [folded, hx, mul_add]
  map_smul' c f := by
    funext x
    by_cases hx : x ≤ 1 <;> ext <;> simp [folded, hx, mul_left_comm]

/-- The extension leaves the original interval unchanged. -/
theorem intervalExtension_left (f : ℝ → ℂ × ℂ) (x : ℝ) (hx : x ≤ 1) :
    intervalExtension b f x = f x := by simp [intervalExtension, folded, hx]

/-- On the second half, the components are swapped and reflected, with the boundary sign. -/
theorem intervalExtension_right (f : ℝ → ℂ × ℂ) (x : ℝ) (hx : 1 < x) :
    intervalExtension b f x = extensionSign b • (f (2 - x)).swap := by
  apply Prod.ext <;> simp [intervalExtension, folded, not_le.mpr hx]

/-- The scalar coefficient of the boundary mode, as a sum of the two half-interval integrals. -/
def intervalAmplitude (f : ℝ → ℂ × ℂ) (n : ℤ) : ℂ :=
  halfCoefficient (fun x => (f x).2) n + extensionSign b * halfCoefficient (fun x => (f x).1) (-n)

/-- The physical second-component coefficient is the boundary-mode amplitude. -/
theorem intervalExtension_coefficient_snd (f : ℝ → ℂ × ℂ) (hf : Continuous f) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b f x).2) n = intervalAmplitude b f n :=
  periodTwoCoefficient_folded (extensionSign b) _ _ hf.snd hf.fst n

/-- The physical first coefficient is the reflected amplitude with the boundary sign. -/
theorem intervalExtension_coefficient_fst (f : ℝ → ℂ × ℂ) (hf : Continuous f) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b f x).1) n =
      extensionSign b * intervalAmplitude b f (-n) := by
  change periodTwoCoefficient (folded (extensionSign b) (fun x => (f x).1) (fun x => (f x).2)) n = _
  rw [periodTwoCoefficient_folded _ _ _ hf.fst hf.snd]
  simp only [intervalAmplitude, neg_neg]
  cases b <;> simp [extensionSign]
  ring

/-- The Fourier coefficients satisfy exactly the already-constructed boundary reflection relation. -/
theorem intervalExtension_coefficient_reflection (f : ℝ → ℂ × ℂ) (hf : Continuous f) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b f x).1) n = extensionSign b *
      periodTwoCoefficient (fun x => (intervalExtension b f x).2) (-n) := by
  rw [intervalExtension_coefficient_fst b f hf n, intervalExtension_coefficient_snd b f hf (-n)]

/-- Period-one finite Fourier synthesis, with both components stored at raw frequencies. -/
def periodOnePair (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (x : ℝ) : ℂ × ℂ :=
  (polynomial a.1 x, polynomial a.2 x)

theorem continuous_periodOnePair (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) : Continuous (periodOnePair a) :=
  (continuous_polynomial a.1).prodMk (continuous_polynomial a.2)

/-- The even coefficient includes the half-normalization and reverses the first raw input index. -/
theorem intervalAmplitude_even (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (l : ℤ) :
    intervalAmplitude b (periodOnePair a) (2 * l) =
      (1 / 2 : ℂ) * (a.2 l + extensionSign b * a.1 (-l)) := by
  change halfCoefficient (polynomial a.2) (2 * l) +
    extensionSign b * halfCoefficient (polynomial a.1) (-(2 * l)) = _
  rw [show -(2 * l) = 2 * (-l) by ring, halfCoefficient_polynomial_even, halfCoefficient_polynomial_even]
  ring

/-- Odd output coefficients are shifted reciprocal sums, with the exact `i/π` normalization. -/
theorem intervalAmplitude_odd (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (l : ℤ) :
    intervalAmplitude b (periodOnePair a) (2 * l + 1) =
      a.2.sum (fun k z => z * (I / ((Real.pi : ℂ) * (2 * k - 2 * l - 1)))) +
      extensionSign b * a.1.sum (fun k z => z * (I / ((Real.pi : ℂ) * (2 * k + 2 * l + 1)))) := by
  change halfCoefficient (polynomial a.2) (2 * l + 1) +
    extensionSign b * halfCoefficient (polynomial a.1) (-(2 * l + 1)) = _
  rw [show -(2 * l + 1) = 2 * (-l - 1) + 1 by ring,
    halfCoefficient_polynomial_odd, halfCoefficient_polynomial_odd]
  apply congrArg (fun z : ℂ =>
    a.2.sum (fun k w => w * (I / ((Real.pi : ℂ) * (2 * k - 2 * l - 1)))) + extensionSign b * z)
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro k hk
  have he : (2 * (k : ℂ) - 2 * ((-l - 1 : ℤ) : ℂ) - 1) = 2 * k + 2 * l + 1 := by
    push_cast
    ring
  dsimp only
  rw [he]

/-- The zero coefficient of a constant pair follows directly from the defining integrals. -/
theorem intervalAmplitude_const_zero (u v : ℂ) :
    intervalAmplitude b (fun _ => (u, v)) 0 = (1 / 2 : ℂ) * (v + extensionSign b * u) := by
  simp [intervalAmplitude, halfCoefficient]
  ring

/-- A one-sided constant input is a direct normalization check for the overlap kernel. -/
theorem intervalAmplitude_oneSided (n : ℤ) :
    intervalAmplitude b (fun _ => ((0 : ℂ), 1)) n = overlap 0 n := by
  simp [intervalAmplitude, halfCoefficient, overlap]

/-- The two-sided unit constant has coefficient one, rather than twice that value. -/
theorem intervalAmplitude_dirichlet_unit_zero :
    intervalAmplitude .dirichlet (fun _ => ((1 : ℂ), 1)) 0 = 1 := by
  rw [intervalAmplitude_const_zero]
  norm_num [extensionSign]

/-- A one-sided constant already produces the reciprocal odd tail in either boundary extension. -/
theorem intervalAmplitude_oneSided_odd (l : ℤ) :
    intervalAmplitude b (fun _ => ((0 : ℂ), 1)) (2 * l + 1) =
      -I / ((Real.pi : ℂ) * (2 * l + 1)) := by
  rw [intervalAmplitude_oneSided, overlap_odd]
  push_cast
  have he : (Real.pi : ℂ) * (2 * 0 - 2 * l - 1) = -((Real.pi : ℂ) * (2 * l + 1)) := by ring
  rw [he, div_neg, neg_div]

end NLS.ZakharovShabat.BoundaryCondition
