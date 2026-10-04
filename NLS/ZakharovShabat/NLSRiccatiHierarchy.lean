import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # The Riccati hierarchy from Appendix H

Index `n` denotes the dissertation's `u_(n+1)`, so the first density is
`-b`. The generating series is formal: no convergence or identification
with the finite-gap Laurent series is assumed here.
-/
noncomputable section
open Set Complex
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The differential-polynomial recurrence of the NLS hierarchy. -/
def nlsRiccatiDensity (a b : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => -b
  | 1 => deriv (-b)
  | n+2 => deriv (nlsRiccatiDensity a b (n+1)) + a *
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        nlsRiccatiDensity a b ij.val.1 * nlsRiccatiDensity a b ij.val.2
termination_by n => n
decreasing_by
  all_goals first | omega | (have h := Finset.mem_antidiagonal.mp ij.property; omega)

@[simp] theorem nlsRiccatiDensity_zero (a b : ℝ → ℂ) : nlsRiccatiDensity a b 0 = -b := by
  rw [nlsRiccatiDensity]

@[simp] theorem nlsRiccatiDensity_one (a b : ℝ → ℂ) : nlsRiccatiDensity a b 1 = -deriv b := by
  rw [nlsRiccatiDensity]
  ext x
  exact deriv.fun_neg

theorem nlsRiccatiDensity_succ_succ (a b : ℝ → ℂ) (n : ℕ) :
    nlsRiccatiDensity a b (n+2) = deriv (nlsRiccatiDensity a b (n+1)) +
      a * ∑ ij ∈ Finset.antidiagonal n, nlsRiccatiDensity a b ij.1 * nlsRiccatiDensity a b ij.2 := by
  rw [nlsRiccatiDensity]
  exact congrArg (fun f : ℝ → ℂ => deriv (nlsRiccatiDensity a b (n+1)) + a*f)
    (Finset.sum_attach (Finset.antidiagonal n) (fun ij : ℕ × ℕ =>
      nlsRiccatiDensity a b ij.1 * nlsRiccatiDensity a b ij.2))

@[simp] theorem nlsRiccatiDensity_two (a b : ℝ → ℂ) :
    nlsRiccatiDensity a b 2 = -deriv (deriv b) + a*b^2 := by
  rw [show 2 = 0+2 from rfl,nlsRiccatiDensity_succ_succ]
  simp only [Nat.zero_add,nlsRiccatiDensity_one,nlsRiccatiDensity_zero,Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton,neg_mul_neg]
  ext x
  simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Pi.neg_apply,deriv.neg]
  ring

/-- The generating series for `u_1,u_2,...`, before multiplication by
inverse spectral frequency. -/
def nlsRiccatiSeries (a b : ℝ → ℂ) : PowerSeries (ℝ → ℂ) :=
  PowerSeries.mk (nlsRiccatiDensity a b)

/-- Coefficientwise spatial differentiation of the formal series. -/
def nlsRiccatiDerivativeSeries (a b : ℝ → ℂ) : PowerSeries (ℝ → ℂ) :=
  PowerSeries.mk (fun n => deriv (nlsRiccatiDensity a b n))

/-- The all-order recurrence is exactly the formal Riccati equation,
with inverse spectral frequency represented by `X`. -/
theorem nlsRiccatiSeries_equation (a b : ℝ → ℂ) :
    nlsRiccatiSeries a b = PowerSeries.C (-b) +
      nlsRiccatiDerivativeSeries a b * PowerSeries.X +
      (PowerSeries.C a * (nlsRiccatiSeries a b * nlsRiccatiSeries a b)) * PowerSeries.X^2 := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | n
  · simp [nlsRiccatiSeries,nlsRiccatiDerivativeSeries]
  · simp [nlsRiccatiSeries,nlsRiccatiDerivativeSeries,PowerSeries.coeff_mul_X_pow']
    rfl
  · change PowerSeries.coeff (n+2) _ = PowerSeries.coeff (n+2) _
    rw [map_add,map_add,PowerSeries.coeff_C,if_neg (by omega)]
    rw [PowerSeries.coeff_mul_X_pow]
    rw [show n+2 = (n+1)+1 by omega,PowerSeries.coeff_succ_mul_X]
    rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_mul]
    simp only [nlsRiccatiSeries,
      nlsRiccatiDerivativeSeries,PowerSeries.coeff_mk,zero_add]
    exact nlsRiccatiDensity_succ_succ a b n

/-- The recurrence determines every coefficient uniquely. This is the
uniqueness step needed when comparing a spectral expansion with the
physical Hamiltonian hierarchy. -/
theorem nlsRiccatiDensity_unique (a b : ℝ → ℂ) (u : ℕ → ℝ → ℂ)
    (hzero : u 0 = -b) (hone : u 1 = deriv (u 0))
    (hrec : ∀ n : ℕ, u (n+2) = deriv (u (n+1)) +
      a * ∑ ij ∈ Finset.antidiagonal n, u ij.1*u ij.2) :
    u = nlsRiccatiDensity a b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa only [nlsRiccatiDensity_zero] using hzero
    · rw [hone,hzero,nlsRiccatiDensity_one]
      ext x
      exact deriv.neg
    · rw [hrec,nlsRiccatiDensity_succ_succ,ih (n+1) (by omega)]
      congr 1
      apply congrArg (fun f : ℝ → ℂ => a*f)
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega),ih ij.2 (by omega)]

/-- Smooth potentials give smooth densities at every order. -/
theorem contDiff_nlsRiccatiDensity (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (n : ℕ) :
    ContDiff ℝ ∞ (nlsRiccatiDensity a b n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa only [nlsRiccatiDensity_zero] using! hb.neg
    · rw [nlsRiccatiDensity_one]
      exact (contDiff_infty_iff_deriv.mp hb).2.neg
    · rw [nlsRiccatiDensity_succ_succ]
      apply (contDiff_infty_iff_deriv.mp (ih (n+1) (by omega))).2.add
      apply ha.mul
      have hs := ContDiff.sum (𝕜 := ℝ) (n := ∞) (s := Finset.antidiagonal n) (f := fun ij =>
        nlsRiccatiDensity a b ij.1 * nlsRiccatiDensity a b ij.2)
      simp only [← Finset.sum_apply] at hs
      apply hs
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      exact (ih ij.1 (by omega)).mul (ih ij.2 (by omega))

/-- The normalized component ratio of the actual classical solution
satisfies the Riccati equation that generates Appendix H. -/
theorem hasDerivAt_classicalRiccatiRatio
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) (hne : (classicalSolution φ z v t).1 ≠ 0) :
    HasDerivAt (fun x : ℝ => I*(classicalSolution φ z v x).2/(classicalSolution φ z v x).1)
      (2*I*z*(I*(classicalSolution φ z v t).2/(classicalSolution φ z v t).1) + (φ t).2 -
        (φ t).1*(I*(classicalSolution φ z v t).2/(classicalSolution φ z v t).1)^2) t := by
  have hd := hasDerivAt_classicalSolution φ z v t
  have h := ((HasFDerivAt.hasDerivAt hd.snd).const_mul I).div
    (HasFDerivAt.hasDerivAt hd.fst) hne
  simp [classicalODECoefficient,smul_eq_mul] at h
  convert! h using 1
  field_simp
  ring_nf
  simp [I_sq]

/-- Integrating the first component's logarithmic derivative is the
source of the Hamiltonian expansion: its correction is `a` times the
same normalized ratio used in the Riccati equation. -/
theorem classicalSolution_fst_logDerivative
    (φ : NLS.LinearVolterra.Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) (hne : (classicalSolution φ z v t).1 ≠ 0) :
    deriv (fun x : ℝ => (classicalSolution φ z v x).1) t / (classicalSolution φ z v t).1 =
      -I*z+(φ t).1*(I*(classicalSolution φ z v t).2/(classicalSolution φ z v t).1) := by
  have hd := (HasFDerivAt.hasDerivAt (hasDerivAt_classicalSolution φ z v t).fst).deriv
  simp [classicalODECoefficient,smul_eq_mul] at hd
  rw [hd]
  field_simp

end NLS.ZakharovShabat
