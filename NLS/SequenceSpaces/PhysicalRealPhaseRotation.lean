import NLS.SequenceSpaces.PhysicalRealDeletedHilbert
import NLS.SequenceSpaces.SignedPairSobolevActions
import NLS.SequenceSpaces.PhaseRotation
import NLS.SequenceSpaces.WeightedPhaseFlow
import NLS.SequenceSpaces.PhysicalRealSobolevInclusion

/-! Odd real frequencies rotate the ACTUAL normalized physical real
mean-zero space, preserving its norm and every quadratic action. -/
noncomputable section
open Set Complex
open scoped ComplexConjugate ENNReal
namespace NLS

def physicalRealPhaseRotation (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j)
    (time : ℝ) (a : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule := by
  let b := Coeff.phaseFlow ω time a.val.val
  have hb0 : b 0=0 := by
    change Complex.exp _*a.val.val 0=0
    have hz : a.val.val 0=0 := a.val.property
    exact (congrArg (fun z : ℂ => Complex.exp (((time*ω 0:ℝ):ℂ)*I)*z) hz).trans (mul_zero _)
  refine ⟨⟨b,hb0⟩,(deletedL2Conjugation_fixed_iff _).mpr
    ((periodOneL2Conjugation_fixed_iff _).mpr ?_)⟩
  intro j
  have hr := (periodOneL2Conjugation_fixed_iff _).mp
    ((deletedL2Conjugation_fixed_iff _).mp a.property)
  change Complex.exp (((time*ω (-j):ℝ):ℂ)*I)*a.val.val (-j)=
    conj (Complex.exp (((time*ω j:ℝ):ℂ)*I)*a.val.val j)
  rw [hr j,map_mul,←Complex.exp_conj,hω j]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

@[simp] theorem physicalRealPhaseRotation_apply
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time : ℝ)
    (a : physicalRealDeletedSubmodule) (j : ℤ) :
    (physicalRealPhaseRotation ω hω time a).val.val j=
      Complex.exp (((time*ω j:ℝ):ℂ)*I)*a.val.val j := rfl

theorem norm_physicalRealPhaseRotation
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    ‖physicalRealPhaseRotation ω hω time a‖=‖a‖ := (Coeff.phaseFlow ω time).norm_map a.val.val

theorem meanZeroWeightedLift_physicalRealPhaseRotation (w : Weight)
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    WeightedCoeff.meanZeroWeightedLiftCLM w (physicalRealPhaseRotation ω hω time a).val=
      WeightedCoeff.phaseFlow w ω time (WeightedCoeff.meanZeroWeightedLiftCLM w a.val) := by
  apply Subtype.ext
  funext j
  rw [WeightedCoeff.meanZeroWeightedLift_apply,physicalRealPhaseRotation_apply,
    WeightedCoeff.phaseFlow_apply,WeightedCoeff.meanZeroWeightedLift_apply]
  ring

@[simp] theorem physicalRealPhaseRotation_zero
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (a : physicalRealDeletedSubmodule) :
    physicalRealPhaseRotation ω hω 0 a=a := by
  apply Subtype.ext
  exact Subtype.ext (Coeff.phaseFlow_zero ω a.val.val)

theorem physicalRealPhaseRotation_add
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time u : ℝ) (a : physicalRealDeletedSubmodule) :
    physicalRealPhaseRotation ω hω time (physicalRealPhaseRotation ω hω u a)=
      physicalRealPhaseRotation ω hω (time+u) a := by
  apply Subtype.ext
  exact Subtype.ext (Coeff.phaseFlow_add ω time u a.val.val)

theorem quadraticActions_physicalRealPhaseRotation
    (e : ℤ ≃ ℕ+) (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    quadraticActionsExponent (q := 1) (deletedToSignedPair e (physicalRealPhaseRotation ω hω time a).val)=
      quadraticActionsExponent (q := 1) (deletedToSignedPair e a.val) := by
  ext k
  rw [quadraticActions_deletedToSignedPair_apply,quadraticActions_deletedToSignedPair_apply,
    physicalRealPhaseRotation_apply,physicalRealPhaseRotation_apply,hω]
  have he : Complex.exp (((time*ω (positiveIndexInjection e k):ℝ):ℂ)*I)*
      Complex.exp (((time*(-ω (positiveIndexInjection e k)):ℝ):ℂ)*I)=1 := by
    rw [←Complex.exp_add]
    have hz : (((time*ω (positiveIndexInjection e k):ℝ):ℂ)*I)+
        (((time*(-ω (positiveIndexInjection e k)):ℝ):ℂ)*I)=0 := by push_cast;ring
    rw [hz,Complex.exp_zero]
  calc
    _=(Complex.exp (((time*ω (positiveIndexInjection e k):ℝ):ℂ)*I)*
      Complex.exp (((time*(-ω (positiveIndexInjection e k)):ℝ):ℂ)*I))*
      (a.val.val (positiveIndexInjection e k)*a.val.val (-positiveIndexInjection e k)) := by ring
    _=_ := by rw [he,one_mul]

theorem physicalRealSobolevInclusion_phaseRotation {s r : ℝ} (h : r≤s)
    (ω : ℤ → ℝ) (hω : ∀ j, ω (-j)= -ω j) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    physicalRealSobolevInclusion h (physicalRealPhaseRotation ω hω time a)=
      physicalRealPhaseRotation ω hω time (physicalRealSobolevInclusion h a) := by
  have hc (b : physicalRealDeletedSubmodule) (j : ℤ) (hj : j≠0) :
      (physicalRealSobolevInclusion h b).val.val j=
        (Weight.sobolev r j:ℂ)*(b.val.val j/(Weight.sobolev s j:ℂ)) := by
    change (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev r)
      (WeightedCoeff.sobolevInclusion h (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s) b.val))).val j=_
    rw [WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj,
      WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.meanZeroWeightedLift_apply]
  apply Subtype.ext
  apply Subtype.ext
  apply lp.ext
  funext j
  by_cases hj : j=0
  · subst j
    exact (physicalRealSobolevInclusion h (physicalRealPhaseRotation ω hω time a)).val.property.trans
      (physicalRealPhaseRotation ω hω time (physicalRealSobolevInclusion h a)).val.property.symm
  · rw [hc _ j hj,physicalRealPhaseRotation_apply,physicalRealPhaseRotation_apply,hc _ j hj]
    ring

theorem continuous_physicalRealPhaseRotation_family
    {X : Type*} [TopologicalSpace X] (ω : X → ℤ → ℝ)
    (hω : ∀ x j, ω x (-j)= -ω x j) (a : X → physicalRealDeletedSubmodule)
    (hωc : ∀ j, Continuous (fun x => ω x j)) (ha : Continuous a) :
    Continuous (fun x : ℝ × X => physicalRealPhaseRotation (ω x.2) (hω x.2) x.1 (a x.2)) := by
  have hc := Coeff.continuous_phaseMultiply_family (p := 2) (by norm_num)
    (fun x : ℝ × X => fun j => x.1*ω x.2 j)
    (fun x : ℝ × X => (a x.2).val.val)
    (fun j => continuous_fst.mul ((hωc j).comp continuous_snd))
    (continuous_subtype_val.comp (continuous_subtype_val.comp (ha.comp continuous_snd)))
  exact (hc.subtype_mk _).subtype_mk _

end NLS
