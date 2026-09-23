import NLS.ZakharovShabat.CanonicalAuxiliaryBoundaryRoots
import NLS.ZakharovShabat.BoundaryCharacteristicAnalytic

/-! # Starred Dirichlet and Neumann characteristic functions
Pulling back the intrinsic ordinary characteristic through the proved phase
conjugation yields entire starred products whose zeros and analytic orders are
exactly those of the actual auxiliary restricted operators.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized characteristic of the actual starred boundary problem. -/
def auxiliaryPeriodOneCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) : ℂ :=
  b.characteristic hp (auxiliaryPeriodOneDirichletPotential hp hp1 φ).val
    (auxiliaryPeriodOneDirichletPotential hp hp1 φ).property z

/-- The starred characteristic is entire in the spectral parameter. -/
theorem analyticOnNhd_auxiliaryPeriodOneCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (auxiliaryPeriodOneCharacteristic hp hp1 b φ) univ :=
  b.analyticOnNhd_characteristic hp hp1 _ _

/-- Its zeros are exactly the actual auxiliary spectrum. -/
theorem auxiliaryPeriodOneCharacteristic_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic hp hp1 b φ z = 0 ↔
      z ∈ b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 φ).val
        (auxiliaryPeriodOnePotential hp hp1 φ).property := by
  rw [b.auxiliarySpectrum_eq]
  exact b.characteristic_eq_zero_iff hp hp1 _ _ z

/-- The analytic order equals the actual auxiliary generalized multiplicity. -/
theorem analyticOrderAt_auxiliaryPeriodOneCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    analyticOrderAt (auxiliaryPeriodOneCharacteristic hp hp1 b φ) z =
      (b.auxiliaryAlgebraicMultiplicity hp (auxiliaryPeriodOnePotential hp hp1 φ).val
        (auxiliaryPeriodOnePotential hp hp1 φ).property z : ℕ∞) := by
  rw [b.auxiliaryAlgebraicMultiplicity_eq]
  exact b.analyticOrderAt_characteristic hp hp1 _ _ z

/-- The normalized starred products have the signed free sine value. -/
@[simp] theorem auxiliaryPeriodOneCharacteristic_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic hp hp1 b (0 : CoeffPair p) z = Complex.sin z := by
  simp only [auxiliaryPeriodOneCharacteristic, map_zero]
  exact b.characteristic_zero hp z

/-- The literal starred product uses all canonical auxiliary coordinates. -/
theorem auxiliaryPeriodOneCharacteristic_eq_canonicalProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) :
    auxiliaryPeriodOneCharacteristic hp hp1 b φ =
      boundaryCharacteristicProduct (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ) :=
  b.characteristic_eq_canonicalProduct hp hp1 _ _

/-- Starred characteristic functions are jointly complex analytic in parameter and potential. -/
theorem analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => auxiliaryPeriodOneCharacteristic hp hp1 b t.2 t.1) univ := by
  let F := auxiliaryPeriodOneDirichletPotential hp hp1
  intro t _
  exact AnalyticAt.comp
    (g := fun a : ℂ × dirichletSubspace (p := p) => b.characteristic hp a.2.val a.2.property a.1)
    (f := fun a : ℂ × CoeffPair p => (a.1,F a.2)) (x := t)
    (analyticOnNhd_boundaryCharacteristic_joint hp hp1 b (t.1,F t.2) (mem_univ _))
    (analyticAt_fst.prod (AnalyticAt.comp (g := F) (f := fun a : ℂ × CoeffPair p => a.2)
      (x := t) (F.analyticAt t.2) analyticAt_snd))

/-- Both parts of the starred analytic claim use the actual auxiliary restricted spectrum. -/
theorem auxiliaryPeriodOneCharacteristic_joint_spec (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => auxiliaryPeriodOneCharacteristic hp hp1 b t.2 t.1) univ ∧
      ∀ (φ : CoeffPair p) (z : ℂ), auxiliaryPeriodOneCharacteristic hp hp1 b φ z = 0 ↔
        z ∈ b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 φ).val
          (auxiliaryPeriodOnePotential hp hp1 φ).property :=
  ⟨analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint hp hp1 b,
    auxiliaryPeriodOneCharacteristic_eq_zero_iff hp hp1 b⟩

end NLS.ZakharovShabat
