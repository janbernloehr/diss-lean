import NLS.SequenceSpaces.PhysicalRealDeletedHilbert
import NLS.SequenceSpaces.PhaseRotation

/-! # Exact signed phase evolution in the original physical weak Hilbert target -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

def deletedPhaseFlow (ω : ℤ → ℝ) (t : ℝ) (b : DeletedCoeff 2 0) : DeletedCoeff 2 0 :=
  ⟨Coeff.phaseFlow ω t b.val,by
    change Complex.exp (((t*ω 0 : ℝ) : ℂ)*I)*b.val 0=0
    have hb : b.val 0=0 := b.property
    rw [hb,mul_zero]⟩

theorem deletedPhaseFlow_real (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (t : ℝ) (b : physicalRealDeletedSubmodule) :
    deletedL2Conjugation (deletedPhaseFlow ω t b.val)=deletedPhaseFlow ω t b.val := by
  have hb := (periodOneL2Conjugation_fixed_iff b.val.val).mp
    ((deletedL2Conjugation_fixed_iff b.val).mp b.property)
  apply (deletedL2Conjugation_fixed_iff _).mpr
  apply (periodOneL2Conjugation_fixed_iff _).mpr
  intro n
  change Complex.exp (((t*ω (-n) : ℝ) : ℂ)*I)*b.val.val (-n)=
    conj (Complex.exp (((t*ω n : ℝ) : ℂ)*I)*b.val.val n)
  rw [hω,hb,map_mul,←Complex.exp_conj]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,ofReal_neg,mul_neg]

def physicalRealDeletedPhaseFlow (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (t : ℝ) (b : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule :=
  ⟨deletedPhaseFlow ω t b.val,deletedPhaseFlow_real ω hω t b⟩

@[simp] theorem physicalRealDeletedPhaseFlow_apply (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (t : ℝ) (b : physicalRealDeletedSubmodule) (j : ℤ) :
    (physicalRealDeletedPhaseFlow ω hω t b).val.val j=
      Complex.exp (((t*ω j : ℝ) : ℂ)*I)*b.val.val j := rfl

theorem continuous_physicalRealDeletedPhaseFlow_family {X : Type*} [TopologicalSpace X]
    (ω : X → ℤ → ℝ) (hodd : ∀ x n, ω x (-n)= -ω x n)
    (z : X → physicalRealDeletedSubmodule)
    (hω : ∀ n, Continuous (fun x => ω x n)) (hz : Continuous z) :
    Continuous (fun x : ℝ × X => physicalRealDeletedPhaseFlow (ω x.2) (hodd x.2) x.1 (z x.2)) := by
  have hc := Coeff.continuous_phaseMultiply_family (by simp : (2 : ℝ≥0∞)≠⊤)
    (fun x : ℝ × X => fun n => x.1*ω x.2 n) (fun x : ℝ × X => (z x.2).val.val)
    (fun n => continuous_fst.mul ((hω n).comp continuous_snd))
    (continuous_subtype_val.comp (continuous_subtype_val.comp (hz.comp continuous_snd)))
  exact (hc.subtype_mk _).subtype_mk _

end NLS
