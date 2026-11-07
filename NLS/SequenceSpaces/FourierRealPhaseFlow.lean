import NLS.Dynamics.ActionDependentWeightedPhaseFlow
import NLS.SequenceSpaces.FourierRealZeroSubmodule

/-! Arbitrary odd real frequencies rotate the genuine physical Fourier
real form, preserving zero mean and all signed coordinate products.
Joint continuity allows pointwise continuously varying unbounded rates. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def fourierRealZeroPhaseFlow (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time : ℝ) (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroSubmodule w p :=
  ⟨⟨phaseFlow w freq time a.val.val,by
    change (phaseFlow w freq time a.val.val).val 0=0
    rw [phaseFlow_apply,show a.val.val.val 0=0 from a.val.property,mul_zero]⟩,by
    intro k
    change (phaseFlow w freq time a.val.val).val (-k)=
      (starRingEnd ℂ) ((phaseFlow w freq time a.val.val).val k)
    rw [phaseFlow_apply,phaseFlow_apply,a.property k]
    simp only [map_mul,← Complex.exp_conj,Complex.conj_I,Complex.conj_ofReal,hf]
    push_cast
    congr 2
    ring⟩

theorem fourierRealZeroPhaseFlow_apply (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time : ℝ) (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroPhaseFlow w freq hf time a).val.val.val k=
      exp (((time*freq k:ℝ):ℂ)*I)*a.val.val.val k := phaseFlow_apply _ _ _ _ _

theorem fourierRealZeroPhaseFlow_zero (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroPhaseFlow w freq hf 0 a=a := by
  apply Subtype.ext
  apply Subtype.ext
  exact phaseFlow_zero w freq a.val.val

theorem fourierRealZeroPhaseFlow_add (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time r : ℝ) (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroPhaseFlow w freq hf time (fourierRealZeroPhaseFlow w freq hf r a)=
      fourierRealZeroPhaseFlow w freq hf (time+r) a := by
  apply Subtype.ext
  apply Subtype.ext
  exact phaseFlow_add w freq time r a.val.val

theorem norm_fourierRealZeroPhaseFlow (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time : ℝ) (a : fourierRealZeroSubmodule w p) :
    ‖fourierRealZeroPhaseFlow w freq hf time a‖=‖a‖ := norm_phaseFlow w freq time a.val.val

theorem fourierRealZeroPhaseFlow_products (w : Weight) (freq : ℤ → ℝ)
    (hf : ∀ k, freq (-k)=-freq k) (time : ℝ) (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealZeroPhaseFlow w freq hf time a).val.val.val k*
        (fourierRealZeroPhaseFlow w freq hf time a).val.val.val (-k)=
      a.val.val.val k*a.val.val.val (-k) := by
  rw [fourierRealZeroPhaseFlow_apply,fourierRealZeroPhaseFlow_apply,hf]
  have he : ((time*freq k:ℝ):ℂ)*I+((time*(-freq k):ℝ):ℂ)*I=0 := by push_cast; ring
  calc
    _ = (exp (((time*freq k:ℝ):ℂ)*I)*exp (((time*(-freq k):ℝ):ℂ)*I))*
        (a.val.val.val k*a.val.val.val (-k)) := by ring
    _ = _ := by rw [← exp_add,he,exp_zero,one_mul]

theorem continuous_fourierRealZeroPhaseFlow_family {X : Type*} [TopologicalSpace X]
    (w : Weight) (hp : p≠⊤) (freq : X → ℤ → ℝ) (hodd : ∀ x k, freq x (-k)=-freq x k)
    (time : X → ℝ) (a : X → fourierRealZeroSubmodule w p)
    (hf : ∀ k, Continuous (fun x => freq x k)) (ht : Continuous time) (ha : Continuous a) :
    Continuous (fun x => fourierRealZeroPhaseFlow w (freq x) (hodd x) (time x) (a x)) := by
  have hA : Continuous (fun x => (a x).val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have h := (continuous_phaseFlow_family w hp freq (fun x => (a x).val.val) hf hA).comp
    (ht.prodMk continuous_id)
  exact (h.subtype_mk _).subtype_mk _

end NLS.WeightedCoeff
