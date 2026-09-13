import NLS.ZakharovShabat.AuxiliaryPhase
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues

/-!
# Physical auxiliary endpoint conditions and phase conjugation

The domains are defined by classical H¹ regularity and the actual endpoint
equations (1.10). The pointwise phase map identifies them with the ordinary
endpoint domains and intertwines the actual differential expressions.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.Fourier

/-- Multiplication by a constant preserves the original interval H¹ regularity. -/
theorem HasIntervalH1Regularity.const_mul {f : ℝ → ℂ} (hf : HasIntervalH1Regularity f) (c : ℂ) :
    HasIntervalH1Regularity (fun x => c * f x) := by
  refine ⟨hf.1.const_smul c, ?_⟩
  simpa only [deriv_const_mul_field', Pi.smul_def, smul_eq_mul] using hf.2.const_smul c

end NLS.Fourier
namespace NLS.ZakharovShabat

/-- Phase rotation of physical functions, before any quotient or Fourier transform. -/
def physicalAuxiliaryPhase : (ℝ → ℂ × ℂ) ≃ₗ[ℂ] (ℝ → ℂ × ℂ) where
  toFun f x := auxiliaryPhase ℂ (f x)
  invFun f x := (auxiliaryPhase ℂ).symm (f x)
  left_inv f := funext fun x => (auxiliaryPhase ℂ).symm_apply_apply (f x)
  right_inv f := funext fun x => (auxiliaryPhase ℂ).apply_symm_apply (f x)
  map_add' f g := funext fun x => map_add (auxiliaryPhase ℂ) (f x) (g x)
  map_smul' c f := funext fun x => map_smul (auxiliaryPhase ℂ) c (f x)

@[simp] theorem physicalAuxiliaryPhase_apply (f : ℝ → ℂ × ℂ) (x : ℝ) :
    physicalAuxiliaryPhase f x = ((f x).1, Complex.I * (f x).2) := rfl

@[simp] theorem physicalAuxiliaryPhase_symm_apply (f : ℝ → ℂ × ℂ) (x : ℝ) :
    physicalAuxiliaryPhase.symm f x = ((f x).1, -Complex.I * (f x).2) := rfl

/-- The potential transformation in the physical conjugation identity. -/
def physicalAuxiliaryPotential (φ : ℝ → ℂ × ℂ) (x : ℝ) : ℂ × ℂ :=
  (Complex.I * (φ x).1, -Complex.I * (φ x).2)

theorem memLp_physicalAuxiliaryPotential (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    MemLp (physicalAuxiliaryPotential φ) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨hφ.fst.const_smul Complex.I, hφ.snd.const_smul (-Complex.I)⟩

/-- Conjugation of the actual differential expression holds pointwise. -/
theorem physicalOperator_auxiliaryPhase (φ f : ℝ → ℂ × ℂ) :
    physicalOperator φ (physicalAuxiliaryPhase f) =
      physicalAuxiliaryPhase (physicalOperator (physicalAuxiliaryPotential φ) f) := by
  funext x
  apply Prod.ext <;>
    simp only [physicalOperator, physicalAuxiliaryPhase_apply, physicalAuxiliaryPotential,
      deriv_const_mul_field]
  · ring
  · ring_nf
    simp

/-- The phase map preserves vanishing on the original closed interval. -/
theorem physicalAuxiliaryPhase_eqOn_zero_iff (f : ℝ → ℂ × ℂ) :
    EqOn (physicalAuxiliaryPhase f) 0 (Icc 0 1) ↔ EqOn f 0 (Icc 0 1) := by
  constructor
  · intro h x hx
    exact (auxiliaryPhase ℂ).injective ((h hx).trans (map_zero _).symm)
  · intro h x hx
    change auxiliaryPhase ℂ (f x) = 0
    rw [h hx]
    exact map_zero _

namespace BoundaryCondition

/-- Original auxiliary H¹ endpoint domain: f₋ + i f₊ = 0 for D*, and
f₋ - i f₊ = 0 for N*, at both endpoints. -/
structure HasClassicalAuxiliaryDomain (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) : Prop where
  fst_regular : HasIntervalH1Regularity (fun x => (f x).1)
  snd_regular : HasIntervalH1Regularity (fun x => (f x).2)
  left : (f 0).1 = -Complex.I * extensionSign b * (f 0).2
  right : (f 1).1 = -Complex.I * extensionSign b * (f 1).2

private theorem phase_endpoint (s z : ℂ) : -Complex.I * s * (Complex.I * z) = s * z := by
  ring_nf
  simp

/-- The source endpoint conditions are equivalent to ordinary conditions after phase rotation. -/
theorem hasClassicalAuxiliaryDomain_phase_iff (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    HasClassicalAuxiliaryDomain b (physicalAuxiliaryPhase f) ↔ HasClassicalIntervalDomain b f := by
  constructor
  · intro h
    refine ⟨h.fst_regular, ?_, ?_, ?_⟩
    · have hs := h.snd_regular.const_mul (-Complex.I)
      simpa [← mul_assoc] using hs
    · simpa only [physicalAuxiliaryPhase_apply, phase_endpoint] using h.left
    · simpa only [physicalAuxiliaryPhase_apply, phase_endpoint] using h.right
  · intro h
    refine ⟨h.fst_regular, h.snd_regular.const_mul Complex.I, ?_, ?_⟩
    · simpa only [physicalAuxiliaryPhase_apply, phase_endpoint] using h.left
    · simpa only [physicalAuxiliaryPhase_apply, phase_endpoint] using h.right

theorem hasClassicalAuxiliaryDomain_iff (b : BoundaryCondition) (f : ℝ → ℂ × ℂ) :
    HasClassicalAuxiliaryDomain b f ↔ HasClassicalIntervalDomain b (physicalAuxiliaryPhase.symm f) := by
  rw [← hasClassicalAuxiliaryDomain_phase_iff, LinearEquiv.apply_symm_apply]

/-- The physical auxiliary eigenvalue set uses only the differential equation,
regularity, nonvanishing, and the original endpoint conditions. -/
def classicalAuxiliaryEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ) : Set ℂ :=
  {z | ∃ f : ℝ → ℂ × ℂ, HasClassicalAuxiliaryDomain b f ∧ ¬ EqOn f 0 (Icc 0 1) ∧
    physicalOperator φ f =ᵐ[volume.restrict (Ioc 0 1)] (fun x => z • f x)}

/-- Physical phase conjugation identifies the original auxiliary eigenvalue sets. -/
theorem classicalAuxiliaryEigenvalues_eq (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ) :
    classicalAuxiliaryEigenvalues b φ = classicalEigenvalues b (physicalAuxiliaryPotential φ) := by
  ext z
  constructor
  · rintro ⟨f, hf, hne, he⟩
    let g := physicalAuxiliaryPhase.symm f
    have hg : physicalAuxiliaryPhase g = f := physicalAuxiliaryPhase.apply_symm_apply f
    refine ⟨g, (hasClassicalAuxiliaryDomain_iff b f).mp hf, ?_, ?_⟩
    · intro h
      exact hne (hg ▸ (physicalAuxiliaryPhase_eqOn_zero_iff g).mpr h)
    · rw [← hg, physicalOperator_auxiliaryPhase] at he
      filter_upwards [he] with x hx
      apply (auxiliaryPhase ℂ).injective
      exact hx.trans (map_smul (auxiliaryPhase ℂ) z (g x)).symm
  · rintro ⟨f, hf, hne, he⟩
    refine ⟨physicalAuxiliaryPhase f, (hasClassicalAuxiliaryDomain_phase_iff b f).mpr hf,
      fun h => hne ((physicalAuxiliaryPhase_eqOn_zero_iff f).mp h), ?_⟩
    rw [physicalOperator_auxiliaryPhase]
    filter_upwards [he] with x hx
    change auxiliaryPhase ℂ (physicalOperator (physicalAuxiliaryPotential φ) f x) = _
    rw [hx, map_smul]
    rfl

theorem isClosed_classicalAuxiliaryEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : IsClosed (classicalAuxiliaryEigenvalues b φ) := by
  rw [classicalAuxiliaryEigenvalues_eq]
  exact isClosed_classicalEigenvalues b _ (memLp_physicalAuxiliaryPotential φ hφ)

theorem discreteTopology_classicalAuxiliaryEigenvalues (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : DiscreteTopology (classicalAuxiliaryEigenvalues b φ) := by
  rw [classicalAuxiliaryEigenvalues_eq]
  exact discreteTopology_classicalEigenvalues b _ (memLp_physicalAuxiliaryPotential φ hφ)

theorem finite_classicalAuxiliaryEigenvalues_inter_of_isBounded (b : BoundaryCondition)
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (classicalAuxiliaryEigenvalues b φ ∩ K) := by
  rw [classicalAuxiliaryEigenvalues_eq]
  exact finite_classicalEigenvalues_inter_of_isBounded b _ (memLp_physicalAuxiliaryPotential φ hφ) hK

end BoundaryCondition
end NLS.ZakharovShabat
