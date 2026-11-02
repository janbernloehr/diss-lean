import NLS.MKdV.MiuraClassicalSolution

/-! # Transfer of the actual spectral solution's Floquet boundary condition

At nonzero spectral parameter the Miura state map is injective. Equal endpoint
values of u therefore give the same Floquet multiplier for the actual ZS
solution and its scalar Miura state. This does not assume a Hill discriminant
identification, and does not yet supply the independent Hill IVP comparison.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.MKdV

/-- Convert an original ZS vector to scalar position and derivative data. -/
def miuraStateMap (u z : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  let A := ContinuousLinearMap.fst ℂ ℂ ℂ+I • ContinuousLinearMap.snd ℂ ℂ ℂ
  let B := ContinuousLinearMap.fst ℂ ℂ ℂ-I • ContinuousLinearMap.snd ℂ ℂ ℂ
  A.prod (u • A-(I*z) • B)

@[simp] theorem miuraStateMap_apply (u z : ℂ) (v : ℂ × ℂ) :
    miuraStateMap u z v = (v.1+I*v.2, u*(v.1+I*v.2)-I*z*(v.1-I*v.2)) := rfl

/-- Nonzero spectral parameter prevents loss of the original initial data. -/
theorem miuraStateMap_injective (u z : ℂ) (hz : z ≠ 0) :
    Function.Injective (miuraStateMap u z) := by
  intro v w h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change v.1+I*v.2 = w.1+I*w.2 at h1
  change u*(v.1+I*v.2)-I*z*(v.1-I*v.2) =
    u*(w.1+I*w.2)-I*z*(w.1-I*w.2) at h2
  have he : (2*I^2*z)*(v.2-w.2) = 0 := by
    linear_combination h2-(u-I*z)*h1
  have hn : 2*I^2*z ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero _ I_ne_zero)) hz
  have hs : v.2 = w.2 := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hn)
  rw [hs] at h1
  exact Prod.ext (add_right_cancel h1) hs

/-- The scalar position and actual derivative of the constructed solution. -/
def classicalMiuraState (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (x : ℝ) : ℂ × ℂ :=
  (classicalMiuraSolution φ z v x, deriv (classicalMiuraSolution φ z v) x)

theorem classicalMiuraState_eq
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t)) (t : Icc (0 : ℝ) 1) :
    classicalMiuraState φ z v t = miuraStateMap (u t) z (classicalSolution φ z v t) := by
  apply Prod.ext
  · rfl
  · exact (hasDerivAt_classicalMiuraSolution φ u z v hφ t).deriv

/-- Every Floquet boundary multiplier transfers in both directions for this
actual solution when u has matching endpoint values and z is nonzero. -/
theorem miura_floquet_condition_iff
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z μ : ℂ) (v : ℂ × ℂ)
    (hφ : ∀ t : Icc (0 : ℝ) 1, φ t = (u t,u t)) (hu : u 1 = u 0) (hz : z ≠ 0) :
    classicalSolution φ z v 1 = μ • v ↔
      classicalMiuraState φ z v 1 = μ • classicalMiuraState φ z v 0 := by
  have h0 := classicalMiuraState_eq φ u z v hφ ⟨0,by constructor <;> norm_num⟩
  have h1 := classicalMiuraState_eq φ u z v hφ ⟨1,by constructor <;> norm_num⟩
  simp only [classicalSolution_zero] at h0
  change classicalMiuraState φ z v 0 = miuraStateMap (u 0) z v at h0
  change classicalMiuraState φ z v 1 = miuraStateMap (u 1) z (classicalSolution φ z v 1) at h1
  rw [h1, h0, hu, ← map_smul]
  exact ⟨fun h => congrArg (miuraStateMap (u 0) z) h,
    fun h => miuraStateMap_injective (u 0) z hz h⟩

end NLS.MKdV
