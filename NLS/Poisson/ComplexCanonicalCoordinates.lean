import NLS.Poisson.RegularSourceCotangentAlgebra
import NLS.Dynamics.ComplexBirkhoffCoordinates

/-! # Complex normalization of canonical rectangular cotangents

For the source sign {x_n,y_m}=-δ_nm, the variables
z_n=(x_n-iy_n)/sqrt(2), w_n=(x_n+iy_n)/sqrt(2) have
{z_n,w_m}=-iδ_nm. The cotangents retain verified Hilbert
Fourier witnesses, so all brackets are absolutely convergent. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Poisson
open Complex Birkhoff RegularSourceCotangent
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The differential of the negative-phase complex coordinate. -/
def complexMinusCotangent (X Y : RegularSourceCotangent p) : RegularSourceCotangent p :=
  (X.smul complexCoordinateScale).add (Y.smul (-complexCoordinateScale*I))

/-- The differential of the positive-phase complex coordinate. -/
def complexPlusCotangent (X Y : RegularSourceCotangent p) : RegularSourceCotangent p :=
  (X.smul complexCoordinateScale).add (Y.smul (complexCoordinateScale*I))

/-- The square-root normalization has exactly square one-half. -/
theorem complexCoordinateScale_square : complexCoordinateScale^2 = (1/2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  rw [complexCoordinateScale,inv_pow,h]
  norm_num

/-- All complex canonical brackets follow from the verified rectangular ones. -/
theorem complex_canonical_of_rectangular (X Y : ℤ → RegularSourceCotangent p)
    (h : ∀ n m, (X n).bivector (X m) = 0 ∧
      (X n).bivector (Y m) = -(if n=m then 1 else 0) ∧ (Y n).bivector (Y m) = 0)
    (n m : ℤ) :
    (complexMinusCotangent (X n) (Y n)).bivector (complexMinusCotangent (X m) (Y m)) = 0 ∧
    (complexMinusCotangent (X n) (Y n)).bivector (complexPlusCotangent (X m) (Y m)) =
      -I*(if n=m then 1 else 0) ∧
    (complexPlusCotangent (X n) (Y n)).bivector (complexPlusCotangent (X m) (Y m)) = 0 := by
  have hyx : (Y n).bivector (X m) = (if n=m then 1 else 0) := by
    rw [bivector_antisymm,(h m n).2.1,neg_neg]
    simp only [eq_comm]
  have hb := bivector_linear_combination_of_canonical (X n) (Y n) (X m) (Y m)
    (if n=m then 1 else 0) complexCoordinateScale (-complexCoordinateScale*I)
    complexCoordinateScale (complexCoordinateScale*I) (h n m).1 (h n m).2.2 hyx (h n m).2.1
  constructor
  · unfold complexMinusCotangent
    rw [bivector_linear_combination_of_canonical _ _ _ _ _ _ _ _ _
      (h n m).1 (h n m).2.2 hyx (h n m).2.1]
    ring
  constructor
  · unfold complexMinusCotangent complexPlusCotangent
    rw [hb]
    have he : -complexCoordinateScale*I*complexCoordinateScale-
        complexCoordinateScale*(complexCoordinateScale*I) = -I := by
      calc
        _ = -2*I*complexCoordinateScale^2 := by ring
        _ = -I := by rw [complexCoordinateScale_square]; ring
    rw [he]
  · unfold complexPlusCotangent
    rw [bivector_linear_combination_of_canonical _ _ _ _ _ _ _ _ _
      (h n m).1 (h n m).2.2 hyx (h n m).2.1]
    ring
end NLS.Poisson

namespace NLS.Poisson.RegularSourceCotangent
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
/-- Regular cotangents use the ordinary source bracket wherever that bracket is defined. -/
theorem bivector_eq_sourceBivector (hp2 : (2 : ℝ≥0∞) ≤ p) (L M : RegularSourceCotangent p) :
    L.bivector M = sourceBivector hp2 L.toCotangent M.toCotangent := by
  exact (bivector_congr (L := L) (L' := ofCotangent hp2 L.toCotangent)
    (M := M) (M' := ofCotangent hp2 M.toCotangent) rfl rfl).trans
      (bivector_ofCotangent hp2 L.toCotangent M.toCotangent)
end NLS.Poisson.RegularSourceCotangent
