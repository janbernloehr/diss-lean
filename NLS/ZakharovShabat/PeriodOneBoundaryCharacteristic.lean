import NLS.ZakharovShabat.BoundaryCharacteristicOrders
import NLS.ZakharovShabat.FreeBoundaryCharacteristic

/-!
# Intrinsic boundary characteristics of source period-one potentials
The ordinary interval extension pulls the intrinsic Dirichlet and Neumann
functions back to the source coefficient space. These statements concern
entirety in the spectral variable; joint parameter analyticity remains separate.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Section 9 ordinary boundary characteristic of an original period-one potential. -/
def periodOneBoundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ) : ℂ :=
  b.characteristic hp (periodOneBoundaryPotential hp hp1 φ).val
    (periodOneBoundaryPotential hp hp1 φ).property z

/-- The source boundary characteristic is entire in its spectral parameter. -/
theorem analyticOnNhd_periodOneBoundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) : AnalyticOnNhd ℂ (periodOneBoundaryCharacteristic hp hp1 b φ) univ :=
  b.analyticOnNhd_characteristic hp hp1 _ _

/-- Its zeros are exactly the boundary spectrum of the proved source interval realization. -/
theorem periodOneBoundaryCharacteristic_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ) : periodOneBoundaryCharacteristic hp hp1 b φ z = 0 ↔
      z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property :=
  b.characteristic_eq_zero_iff hp hp1 _ _ z

/-- Source characteristic orders agree with the original restricted-operator multiplicities. -/
theorem analyticOrderAt_periodOneBoundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (z : ℂ) : analyticOrderAt (periodOneBoundaryCharacteristic hp hp1 b φ) z =
      (b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
        (periodOneBoundaryPotential hp hp1 φ).property z : ℕ∞) :=
  b.analyticOrderAt_characteristic hp hp1 _ _ z

/-- Both source boundary characteristics reduce to sine at zero potential. -/
theorem periodOneBoundaryCharacteristic_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b (0 : CoeffPair p) z = Complex.sin z := by
  simp only [periodOneBoundaryCharacteristic,map_zero]
  exact b.characteristic_zero hp z

/-- Any complete source boundary labeling gives the intrinsic source characteristic product. -/
theorem periodOneBoundaryCharacteristic_eq_product (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (N : ℕ) (ξ : ℤ → ℂ)
    (h : BoundaryRootLabeling b hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property N ξ) :
    periodOneBoundaryCharacteristic hp hp1 b φ = boundaryCharacteristicProduct ξ :=
  h.product_eq_characteristic.symm

end NLS.ZakharovShabat
