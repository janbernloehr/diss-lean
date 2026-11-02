import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Derivation.Basic

/-! # Extending a coefficient derivation to formal power series

This derivative acts on the coefficients and leaves the formal spectral
parameter fixed. It is distinct from differentiation in the series variable.
-/
noncomputable section
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Apply an algebra derivation coefficientwise, keeping X fixed. -/
def powerSeriesDerivation (D : Derivation K A A) :
    Derivation K (PowerSeries A) (PowerSeries A) where
  toFun f := PowerSeries.mk (fun n => D (PowerSeries.coeff n f))
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp
  map_one_eq_zero' := by
    change PowerSeries.mk (fun n => D (PowerSeries.coeff n (1 : PowerSeries A))) = 0
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, map_zero]
    split_ifs <;> simp
  leibniz' f g := by
    change PowerSeries.mk (fun n => D (PowerSeries.coeff n (f*g))) =
      f*PowerSeries.mk (fun n => D (PowerSeries.coeff n g)) +
        g*PowerSeries.mk (fun n => D (PowerSeries.coeff n f))
    rw [mul_comm g (PowerSeries.mk _)]
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, map_sum,
      Derivation.leibniz, smul_eq_mul, map_add]
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij _
    ring

@[simp] theorem coeff_powerSeriesDerivation (D : Derivation K A A) (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesDerivation D f) = D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk (fun j => D (PowerSeries.coeff j f))) = _
  exact PowerSeries.coeff_mk _ _

@[simp] theorem powerSeriesDerivation_C (D : Derivation K A A) (a : A) :
    powerSeriesDerivation D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  simp only [coeff_powerSeriesDerivation, PowerSeries.coeff_C]
  split_ifs <;> simp

@[simp] theorem powerSeriesDerivation_X (D : Derivation K A A) :
    powerSeriesDerivation D (PowerSeries.X : PowerSeries A) = 0 := by
  ext n
  simp only [coeff_powerSeriesDerivation, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp

/-- Commuting coefficient derivations still commute on the entire series. -/
theorem powerSeriesDerivation_commute (D E : Derivation K A A)
    (h : ∀ a, E (D a) = D (E a)) (f : PowerSeries A) :
    powerSeriesDerivation E (powerSeriesDerivation D f) =
      powerSeriesDerivation D (powerSeriesDerivation E f) := by
  ext n
  simpa only [coeff_powerSeriesDerivation] using h (PowerSeries.coeff n f)

end NLS.DifferentialPolynomial
