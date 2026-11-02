import NLS.DifferentialPolynomial.PowerSeriesDerivation
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Explicit primitives of formal logarithmic derivatives

Only finitely many logarithm terms contribute to each coefficient. This
construction uses no convergence assumption on the formal series.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

/-- Coefficient n of log(1+X R)/X, using its finite Taylor formula. -/
def logarithmicPrimitiveCoefficient (R : PowerSeries A) (n : ℕ) : A :=
  PowerSeries.coeff n (∑ k ∈ Finset.range (n+1),
    PowerSeries.C (algebraMap K A ((-1 : K)^k/(k+1 : K)))*R^(k+1)*PowerSeries.X^k)

private theorem logarithmic_scalar_cancel (k : ℕ) :
    algebraMap K A ((-1 : K)^k/(k+1 : K))*(k+1 : A) = (-1 : A)^k := by
  have hk : (k+1 : K) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  calc
    _ = algebraMap K A (((-1 : K)^k/(k+1 : K))*(k+1 : K)) := by simp
    _ = algebraMap K A ((-1 : K)^k) := by rw [div_mul_cancel₀ _ hk]
    _ = _ := by simp

private theorem derivation_logarithm_term (D : Derivation K A A) (R : PowerSeries A) (k : ℕ) :
    powerSeriesDerivation D
      (PowerSeries.C (algebraMap K A ((-1 : K)^k/(k+1 : K)))*R^(k+1)*PowerSeries.X^k) =
      powerSeriesDerivation D R * (-PowerSeries.X*R)^k := by
  have hx : powerSeriesDerivation D ((PowerSeries.X : PowerSeries A)^k) = 0 := by
    rw [Derivation.leibniz_pow, powerSeriesDerivation_X, smul_zero, smul_zero]
  have hc := logarithmic_scalar_cancel (K := K) (A := A) k
  have hc' : PowerSeries.C (algebraMap K A ((-1 : K)^k/(k+1 : K)))*
      (k+1 : PowerSeries A) = (-1 : PowerSeries A)^k := by
    simpa using congrArg (PowerSeries.C : A →+* PowerSeries A) hc
  simp only [Derivation.leibniz, smul_eq_mul, powerSeriesDerivation_C,
    Derivation.map_algebraMap, map_zero, hx, mul_zero, add_zero,
    Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = (PowerSeries.C (algebraMap K A ((-1 : K)^k/(k+1 : K)))*
        (k+1 : PowerSeries A))*R^k*powerSeriesDerivation D R*PowerSeries.X^k := by ring
    _ = _ := by rw [hc']; ring

/-- Every coefficient of D R/(1+X R) is an explicit coefficient derivative. -/
theorem derivation_logarithmicPrimitiveCoefficient (D : Derivation K A A)
    (R V : PowerSeries A) (hV : (1+PowerSeries.X*R)*V = 1) (n : ℕ) :
    D (logarithmicPrimitiveCoefficient (K := K) R n) =
      PowerSeries.coeff n (powerSeriesDerivation D R*V) := by
  let S : PowerSeries A := ∑ k ∈ Finset.range (n+1), (-PowerSeries.X*R)^k
  have hgeom : S*(1+PowerSeries.X*R) = 1-(-PowerSeries.X*R)^(n+1) := by
    have he := geom_sum_mul_neg (-PowerSeries.X*R) (n+1)
    have ht : (1 : PowerSeries A)-(-PowerSeries.X*R) = 1+PowerSeries.X*R := by ring
    rw [ht] at he
    exact he
  have hS : S = V-V*(-PowerSeries.X*R)^(n+1) := by
    calc
      S = S*((1+PowerSeries.X*R)*V) := by rw [hV, mul_one]
      _ = (S*(1+PowerSeries.X*R))*V := by ring
      _ = _ := by rw [hgeom]; ring
  have htail : PowerSeries.coeff n
      (powerSeriesDerivation D R*V*(-PowerSeries.X*R)^(n+1)) = 0 := by
    have he : powerSeriesDerivation D R*V*(-PowerSeries.X*R)^(n+1) =
        (powerSeriesDerivation D R*V*((-R)^(n+1)))*PowerSeries.X^(n+1) := by ring
    rw [he, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
  change D (PowerSeries.coeff n _) = _
  rw [← coeff_powerSeriesDerivation, map_sum]
  simp_rw [derivation_logarithm_term]
  rw [← Finset.mul_sum]
  change PowerSeries.coeff n (powerSeriesDerivation D R*S) = _
  rw [hS, mul_sub, map_sub, ← mul_assoc, htail, sub_zero]

end NLS.DifferentialPolynomial
