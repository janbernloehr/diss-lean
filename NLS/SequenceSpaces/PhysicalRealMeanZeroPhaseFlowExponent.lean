import NLS.SequenceSpaces.WeightedPhaseFlowFamily
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent

/-! # Exact real Fourier phase flows in the original weighted lp norms -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS
variable (w : Weight) {p : ℝ≥0∞} [Fact (1≤p)]

theorem physicalRealMeanZero_phaseFlow_mem (ω : ℤ → ℝ)
    (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    WeightedCoeff.phaseFlow w ω t z.val∈physicalRealMeanZeroWeightedExponent w p := by
  constructor
  · intro n
    rw [WeightedCoeff.phaseFlow_apply,WeightedCoeff.phaseFlow_apply,hω,z.property.1,
      map_mul,←Complex.exp_conj]
    congr 2
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,ofReal_neg,mul_neg]
  · rw [WeightedCoeff.phaseFlow_apply,z.property.2,mul_zero]

def physicalRealMeanZeroPhaseFlow (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (t : ℝ) (z : physicalRealMeanZeroWeightedExponent w p) :
    physicalRealMeanZeroWeightedExponent w p :=
  ⟨WeightedCoeff.phaseFlow w ω t z.val,physicalRealMeanZero_phaseFlow_mem w ω hω t z⟩

@[simp] theorem physicalRealMeanZeroPhaseFlow_apply
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) (j : ℤ) :
    (physicalRealMeanZeroPhaseFlow w ω hω t z).val.val j=
      Complex.exp (((t*ω j : ℝ) : ℂ)*I)*z.val.val j :=
  WeightedCoeff.phaseFlow_apply w ω t z.val j

@[simp] theorem physicalRealMeanZeroPhaseFlow_zero
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    physicalRealMeanZeroPhaseFlow w ω hω 0 z=z :=
  Subtype.ext (WeightedCoeff.phaseFlow_zero w ω z.val)

theorem physicalRealMeanZeroPhaseFlow_add
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t u : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    physicalRealMeanZeroPhaseFlow w ω hω t (physicalRealMeanZeroPhaseFlow w ω hω u z)=
      physicalRealMeanZeroPhaseFlow w ω hω (t+u) z :=
  Subtype.ext (WeightedCoeff.phaseFlow_add w ω t u z.val)

@[simp] theorem norm_physicalRealMeanZeroPhaseFlow
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    ‖physicalRealMeanZeroPhaseFlow w ω hω t z‖=‖z‖ :=
  WeightedCoeff.norm_phaseFlow w ω t z.val

theorem continuous_physicalRealMeanZeroPhaseFlow_family {X : Type*} [TopologicalSpace X]
    (hp : p≠⊤) (ω : X → ℤ → ℝ) (hodd : ∀ x n, ω x (-n)= -ω x n)
    (z : X → physicalRealMeanZeroWeightedExponent w p)
    (hω : ∀ n, Continuous (fun x => ω x n)) (hz : Continuous z) :
    Continuous (fun x : ℝ × X => physicalRealMeanZeroPhaseFlow w (ω x.2) (hodd x.2) x.1 (z x.2)) := by
  exact (WeightedCoeff.continuous_phaseFlow_family w hp ω (fun x => (z x).val)
    hω (continuous_subtype_val.comp hz)).subtype_mk _

theorem physicalRealMeanZeroPhaseFlow_signed_product
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) (j : ℤ) :
    (physicalRealMeanZeroPhaseFlow w ω hω t z).val.val j*
      (physicalRealMeanZeroPhaseFlow w ω hω t z).val.val (-j)=z.val.val j*z.val.val (-j) := by
  rw [physicalRealMeanZeroPhaseFlow_apply,physicalRealMeanZeroPhaseFlow_apply,hω]
  have he : Complex.exp (((t*ω j : ℝ) : ℂ)*I)*
      Complex.exp (((t*(-ω j) : ℝ) : ℂ)*I)=1 := by
    rw [←Complex.exp_add]
    simp only [mul_neg,ofReal_neg,neg_mul,add_neg_cancel,Complex.exp_zero]
  calc
    _ = (Complex.exp (((t*ω j : ℝ) : ℂ)*I)*Complex.exp (((t*(-ω j) : ℝ) : ℂ)*I))*
      (z.val.val j*z.val.val (-j)) := by ring
    _ = _ := by rw [he,one_mul]

theorem physicalRealMeanZeroPhaseFlow_support
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    Function.support (physicalRealMeanZeroPhaseFlow w ω hω t z).val.val=Function.support z.val.val := by
  ext j
  simp only [Function.mem_support,physicalRealMeanZeroPhaseFlow_apply]
  constructor
  · intro h hz
    exact h (by rw [hz,mul_zero])
  · intro h
    exact mul_ne_zero (Complex.exp_ne_zero _) h

end NLS
