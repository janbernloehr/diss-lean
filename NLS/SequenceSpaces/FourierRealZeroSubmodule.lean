import NLS.SequenceSpaces.WeightedZeroMode
import NLS.SequenceSpaces.ConjugateReflection

/-! The physical real Fourier form of a zero-mode weighted space is the
closed REAL submodule a(-k)=conj(a(k)), with its inherited Banach norm. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

instance zeroModeSubmodule_normedSpaceReal (w : Weight) : NormedSpace ℝ (zeroModeSubmodule w p) :=
  NormedSpace.restrictScalars ℝ ℂ (zeroModeSubmodule w p)

def fourierRealZeroSubmodule (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (zeroModeSubmodule w p) where
  carrier := {a | ∀ k : ℤ, a.val.val (-k)=(starRingEnd ℂ) (a.val.val k)}
  zero_mem' := by intro k; simp
  add_mem' ha hb := by
    intro k
    change _+_=(starRingEnd ℂ) (_+_)
    rw [map_add,ha k,hb k]
  smul_mem' r a ha := by
    intro k
    change (r:ℂ)*a.val.val (-k)=(starRingEnd ℂ) ((r:ℂ)*a.val.val k)
    rw [map_mul,Complex.conj_ofReal,ha k]

instance fourierRealZeroSubmodule_normedSpace (w : Weight) :
    NormedSpace ℝ (fourierRealZeroSubmodule w p) where
  norm_smul_le r a := by
    change ‖(r:ℂ) • a.val.val‖ ≤ ‖r‖*‖a.val.val‖
    rw [norm_smul,Complex.norm_real]

theorem mem_fourierRealZeroSubmodule (w : Weight) (a : zeroModeSubmodule w p) :
    a ∈ fourierRealZeroSubmodule w p ↔ ∀ k : ℤ, a.val.val (-k)=(starRingEnd ℂ) (a.val.val k) := Iff.rfl

theorem isClosed_fourierRealZeroSubmodule (w : Weight) :
    IsClosed (fourierRealZeroSubmodule w p : Set (zeroModeSubmodule w p)) := by
  have he : (fourierRealZeroSubmodule w p : Set (zeroModeSubmodule w p))=
      ⋂ k : ℤ, {a : zeroModeSubmodule w p | a.val.val (-k)=(starRingEnd ℂ) (a.val.val k)} := by
    ext a
    simp only [mem_iInter]
    rfl
  rw [he]
  apply isClosed_iInter
  intro k
  exact isClosed_eq ((evalCLM w p (-k)).continuous.comp (zeroModeSubmodule w p).subtypeL.continuous)
    (Complex.continuous_conj.comp ((evalCLM w p k).continuous.comp (zeroModeSubmodule w p).subtypeL.continuous))

instance fourierRealZeroSubmodule_complete (w : Weight) : CompleteSpace (fourierRealZeroSubmodule w p) :=
  (isClosed_fourierRealZeroSubmodule w).completeSpace_coe

theorem zeroMode_add_val (w : Weight) (a b : zeroModeSubmodule w p) (k : ℤ) :
    (a+b).val.val k=a.val.val k+b.val.val k := rfl

theorem zeroMode_real_smul_val (w : Weight) (r : ℝ) (a : zeroModeSubmodule w p) (k : ℤ) :
    (r • a).val.val k=(r:ℂ)*a.val.val k := rfl

def zeroModeConjugation (w : Weight) (hw : ∀ k, w (-k)=w k) (a : zeroModeSubmodule w p) :
    zeroModeSubmodule w p :=
  ⟨conjugateReflection w hw a.val,by
    change (conjugateReflection w hw a.val).val 0=0
    rw [conjugateReflection_apply,neg_zero,show a.val.val 0=0 from a.property,map_zero]⟩

theorem zeroModeConjugation_apply (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : zeroModeSubmodule w p) (k : ℤ) :
    (zeroModeConjugation w hw a).val.val k=(starRingEnd ℂ) (a.val.val (-k)) :=
  conjugateReflection_apply w hw a.val k

def zeroModeConjugationCLM (w : Weight) (hw : ∀ k, w (-k)=w k) :
    zeroModeSubmodule w p →L[ℝ] zeroModeSubmodule w p :=
  LinearMap.mkContinuous
    { toFun := zeroModeConjugation w hw
      map_add' a b := by
        apply Subtype.ext
        apply Subtype.ext
        funext k
        simp only [zeroModeConjugation_apply,zeroMode_add_val,map_add]
      map_smul' r a := by
        apply Subtype.ext
        apply Subtype.ext
        funext k
        simp only [RingHom.id_apply,zeroModeConjugation_apply,zeroMode_real_smul_val,map_mul,Complex.conj_ofReal] }
    1 (fun a => by
      change ‖conjugateReflection w hw a.val‖ ≤ 1*‖a.val‖
      rw [norm_conjugateReflection,one_mul])

end NLS.WeightedCoeff
