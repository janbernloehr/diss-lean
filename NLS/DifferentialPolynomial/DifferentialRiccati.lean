import NLS.DifferentialPolynomial.PowerSeriesDerivation
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # The canonical Riccati series in a differential algebra -/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- The uniquely determined Riccati coefficients for a coefficient derivation. -/
def differentialRiccatiSequence (D : Derivation K A A) (a b : A) : ℕ → A
  | 0 => -b
  | 1 => D (-b)
  | n+2 => D (differentialRiccatiSequence D a b (n+1)) + a *
      ∑ ij ∈ (Finset.antidiagonal n).attach,
        differentialRiccatiSequence D a b ij.val.1 * differentialRiccatiSequence D a b ij.val.2
termination_by n => n
decreasing_by
  all_goals first | omega | (have h := Finset.mem_antidiagonal.mp ij.property; omega)

@[simp] theorem differentialRiccatiSequence_zero (D : Derivation K A A) (a b : A) :
    differentialRiccatiSequence D a b 0 = -b := by rw [differentialRiccatiSequence]

@[simp] theorem differentialRiccatiSequence_one (D : Derivation K A A) (a b : A) :
    differentialRiccatiSequence D a b 1 = D (-b) := by rw [differentialRiccatiSequence]

theorem differentialRiccatiSequence_recurrence (D : Derivation K A A) (a b : A) (n : ℕ) :
    differentialRiccatiSequence D a b (n+2) = D (differentialRiccatiSequence D a b (n+1)) +
      a * ∑ ij ∈ Finset.antidiagonal n,
        differentialRiccatiSequence D a b ij.1 * differentialRiccatiSequence D a b ij.2 := by
  rw [differentialRiccatiSequence]
  congr 1
  exact congrArg (fun x : A => a*x) (Finset.sum_attach (Finset.antidiagonal n)
    (fun ij : ℕ × ℕ =>
      differentialRiccatiSequence D a b ij.1*differentialRiccatiSequence D a b ij.2))

theorem differentialRiccatiSequence_unique (D : Derivation K A A) (a b : A) (u : ℕ → A)
    (h0 : u 0 = -b) (h1 : u 1 = D (u 0))
    (hrec : ∀ n, u (n+2) = D (u (n+1)) +
      a * ∑ ij ∈ Finset.antidiagonal n, u ij.1*u ij.2) :
    u = differentialRiccatiSequence D a b := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simpa using h0
    · simpa [h0] using h1
    · rw [hrec, differentialRiccatiSequence_recurrence, ih (n+1) (by omega)]
      congr 1
      apply congrArg (fun x : A => a*x)
      apply Finset.sum_congr rfl
      intro ij hij
      have he := Finset.mem_antidiagonal.mp hij
      rw [ih ij.1 (by omega), ih ij.2 (by omega)]

def differentialRiccatiSeries (D : Derivation K A A) (a b : A) : PowerSeries A :=
  PowerSeries.mk (differentialRiccatiSequence D a b)

@[simp] theorem coeff_differentialRiccatiSeries (D : Derivation K A A) (a b : A) (n : ℕ) :
    PowerSeries.coeff n (differentialRiccatiSeries D a b) = differentialRiccatiSequence D a b n :=
  PowerSeries.coeff_mk _ _

/-- The constructed series satisfies the Riccati equation at every order. -/
theorem differentialRiccatiSeries_equation (D : Derivation K A A) (a b : A) :
    differentialRiccatiSeries D a b = PowerSeries.C (-b) +
      powerSeriesDerivation D (differentialRiccatiSeries D a b) * PowerSeries.X +
      (PowerSeries.C a * (differentialRiccatiSeries D a b * differentialRiccatiSeries D a b)) *
        PowerSeries.X^2 := by
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | n
  · simp
  · simp [PowerSeries.coeff_mul_X_pow']
  · change PowerSeries.coeff (n+2) _ = PowerSeries.coeff (n+2) _
    rw [map_add, map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add,
      PowerSeries.coeff_mul_X_pow]
    rw [show n+2 = (n+1)+1 by omega, PowerSeries.coeff_succ_mul_X]
    rw [PowerSeries.coeff_C_mul]
    simp only [coeff_powerSeriesDerivation, coeff_differentialRiccatiSeries,
      PowerSeries.coeff_mul]
    exact differentialRiccatiSequence_recurrence D a b n

theorem differentialRiccatiSequence_neg_derivation (D : Derivation K A A) (a b : A) (n : ℕ) :
    differentialRiccatiSequence (-D) a b n = (-1 : A)^n*differentialRiccatiSequence D a b n := by
  have hp (k : ℕ) : D ((-1 : A)^k) = 0 := by
    rw [Derivation.leibniz_pow]
    simp
  have he := differentialRiccatiSequence_unique (-D) a b
    (fun k => (-1 : A)^k*differentialRiccatiSequence D a b k)
    (by simp) (by simp [Derivation.neg_apply]) (by
      intro k
      have hs : (∑ ij ∈ Finset.antidiagonal k,
          ((-1 : A)^ij.1*differentialRiccatiSequence D a b ij.1)*
            ((-1 : A)^ij.2*differentialRiccatiSequence D a b ij.2)) =
          (-1 : A)^k * ∑ ij ∈ Finset.antidiagonal k,
            differentialRiccatiSequence D a b ij.1*differentialRiccatiSequence D a b ij.2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ij hij
        rw [mul_mul_mul_comm, ← pow_add, Finset.mem_antidiagonal.mp hij]
      rw [differentialRiccatiSequence_recurrence, hs]
      simp only [Derivation.neg_apply, Derivation.leibniz, smul_eq_mul, hp]
      simp only [pow_add, pow_one, pow_two]
      ring)
  exact (congrFun he n).symm

theorem differentialRiccatiSeries_neg_derivation (D : Derivation K A A) (a b : A) :
    differentialRiccatiSeries (-D) a b =
      PowerSeries.rescale (-1) (differentialRiccatiSeries D a b) := by
  ext n
  simp [differentialRiccatiSequence_neg_derivation]

@[simp] theorem powerSeriesDerivation_neg (D : Derivation K A A) (f : PowerSeries A) :
    powerSeriesDerivation (-D) f = -(powerSeriesDerivation D f) := by
  ext n
  simp

end NLS.DifferentialPolynomial
