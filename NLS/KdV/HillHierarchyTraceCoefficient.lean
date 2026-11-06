import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! # The source nonlinear convolution is the formal squared-phase coefficient. Actual contour identification is separate. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial Complex
namespace NLS.KdV

/-- Source Lemma 4, with an empty convolution at m=0 and m=1. -/
def hillHierarchyTraceCoefficient (H : ℕ → ℂ) (m : ℕ) : ℂ :=
  H m / 4^m - 2 / 4^m *
    (if 2 ≤ m then ∑ ij ∈ Finset.antidiagonal (m-2), H ij.1 * H ij.2 else 0)

def hillFormalHamiltonianSeries (H : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => H m / 4^(m+1))

/-- The correction to F²/λ in the formal inverse-energy variable. -/
def hillFormalSquaredPhase (H : ℕ → ℂ) : PowerSeries ℂ :=
  (PowerSeries.C 2 * hillFormalHamiltonianSeries H)*PowerSeries.X^2 -
    (hillFormalHamiltonianSeries H * hillFormalHamiltonianSeries H)*PowerSeries.X^4

theorem hillFormalHamiltonianSeries_square_coeff (H : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (hillFormalHamiltonianSeries H * hillFormalHamiltonianSeries H) =
      (∑ ij ∈ Finset.antidiagonal n, H ij.1 * H ij.2) / 4^(n+2) := by
  rw [PowerSeries.coeff_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ij hij
  have h := Finset.mem_antidiagonal.mp hij
  simp only [hillFormalHamiltonianSeries, PowerSeries.coeff_mk]
  rw [div_mul_div_comm, ← pow_add]
  congr 2
  omega

theorem coeff_hillFormalSquaredPhase (H : ℕ → ℂ) (m : ℕ) :
    2 * PowerSeries.coeff (m+2) (hillFormalSquaredPhase H) =
      hillHierarchyTraceCoefficient H m := by
  rcases m with _ | _ | n
  · simp [hillFormalSquaredPhase, hillFormalHamiltonianSeries,
      hillHierarchyTraceCoefficient, PowerSeries.coeff_mul_X_pow']
    ring
  · simp [hillFormalSquaredPhase, hillFormalHamiltonianSeries,
      hillHierarchyTraceCoefficient, PowerSeries.coeff_mul_X_pow']
    ring
  · rw [hillFormalSquaredPhase, map_sub, PowerSeries.coeff_mul_X_pow]
    rw [show n+1+1+2 = n+4 by omega, PowerSeries.coeff_mul_X_pow]
    rw [PowerSeries.coeff_C_mul, hillFormalHamiltonianSeries_square_coeff]
    simp only [hillFormalHamiltonianSeries, PowerSeries.coeff_mk,
      hillHierarchyTraceCoefficient, show 2 ≤ n+1+1 by omega, ↓reduceIte,
      show n+1+1-2 = n by omega]
    rw [show n+1+1+1 = (n+2)+1 by omega, pow_succ]
    ring

@[simp] theorem hillHierarchyTraceCoefficient_zero (H : ℕ → ℂ) :
    hillHierarchyTraceCoefficient H 0 = H 0 := by simp [hillHierarchyTraceCoefficient]

@[simp] theorem hillHierarchyTraceCoefficient_one (H : ℕ → ℂ) :
    hillHierarchyTraceCoefficient H 1 = H 1/4 := by simp [hillHierarchyTraceCoefficient]

@[simp] theorem hillHierarchyTraceCoefficient_two (H : ℕ → ℂ) :
    hillHierarchyTraceCoefficient H 2 = H 2/16-(H 0)^2/8 := by
  simp [hillHierarchyTraceCoefficient]
  ring

end NLS.KdV
