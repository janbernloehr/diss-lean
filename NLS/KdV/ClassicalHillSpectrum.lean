import NLS.KdV.ClassicalHillFlow
import NLS.KdV.ClassicalLocalPrimitive

/-! # Actual scalar Floquet spectra and the Hill discriminant

The scalar IVP is the shared flow from the Hill estimates branch. The
invertible constant-upper state transformation transfers the original
monodromy characteristic equation, including at zero energy. Thus the
radicand's zeros detect actual periodic or antiperiodic scalar solutions.
The period-two Fourier-domain spectral equivalence remains separate.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- The exact scalar Floquet characteristic criterion, at every energy
and every multiplier. The scalar solution is the actual constructed IVP. -/
theorem classicalHill_characteristic_eq_zero_iff
    (q : NLS.LinearVolterra.Curve ℂ) (lambda σ : ℂ) :
    σ^2-σ*classicalHillDiscriminant q lambda+1 = 0 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = σ • v := by
  obtain ⟨z,rfl⟩ := IsAlgClosed.exists_pow_nat_eq lambda (by norm_num : 0 < 2)
  have ht : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hflow (v : ℂ × ℂ) :
      classicalHillFlow q (z^2) (constantUpperStateMap z v) 1 =
        constantUpperStateMap z (classicalSolution (constantUpperPotential q) z v 1) := by
    rw [classicalHillFlow_eq_constantUpper q z (constantUpperStateMap z v) ⟨1,ht⟩,
      constantUpperInitialVector_stateMap]
  have h := det_classicalMonodromy_sub_scalar_eq_zero_iff (constantUpperPotential q) z σ
  rw [det_classicalMonodromy_sub_scalar] at h
  rw [classicalHillDiscriminant_sq]
  constructor
  · intro he
    obtain ⟨v,hv,hvσ⟩ := h.mp he
    refine ⟨constantUpperStateMap z v,?_,?_⟩
    · exact fun hz => hv (constantUpperStateMap_injective z (hz.trans (map_zero _).symm))
    · rw [hflow,hvσ,map_smul]
  · rintro ⟨w,hw,hwσ⟩
    apply h.mpr
    refine ⟨constantUpperInitialVector z w,?_,?_⟩
    · intro hz
      apply hw
      have he := congrArg (constantUpperStateMap z) hz
      simpa only [constantUpperStateMap_initialVector,map_zero] using he
    apply constantUpperStateMap_injective z
    rw [map_smul,← hflow,constantUpperStateMap_initialVector]
    exact hwσ

theorem classicalHillDiscriminant_eq_two_iff (q : NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) :
    classicalHillDiscriminant q lambda = 2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = v := by
  have h := classicalHill_characteristic_eq_zero_iff q lambda 1
  have he : (1 : ℂ)^2-1*classicalHillDiscriminant q lambda+1 =
      2-classicalHillDiscriminant q lambda := by ring
  rw [he,sub_eq_zero,eq_comm] at h
  simpa only [one_smul] using h

theorem classicalHillDiscriminant_eq_neg_two_iff (q : NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) :
    classicalHillDiscriminant q lambda = -2 ↔
      ∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = -v := by
  have h := classicalHill_characteristic_eq_zero_iff q lambda (-1)
  have he : (-1 : ℂ)^2-(-1)*classicalHillDiscriminant q lambda+1 =
      classicalHillDiscriminant q lambda+2 := by ring
  simpa only [he,add_eq_zero_iff_eq_neg,neg_one_smul] using h

/-- Branch points are exactly the actual scalar periodic or
antiperiodic spectral values, with no simplicity hypothesis. -/
theorem classicalHillRadicand_eq_zero_iff (q : NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) :
    classicalHillRadicand (lambda,q) = 0 ↔
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = v) ∨
      (∃ v : ℂ × ℂ, v ≠ 0 ∧ classicalHillFlow q lambda v 1 = -v) := by
  rw [← classicalHillDiscriminant_eq_two_iff,← classicalHillDiscriminant_eq_neg_two_iff]
  change classicalHillDiscriminant q lambda ^ 2-4 = 0 ↔ _
  rw [sub_eq_zero,show (4 : ℂ) = 2^2 by norm_num,sq_eq_sq_iff_eq_or_eq_neg]

end NLS.KdV
