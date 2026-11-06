import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Raw complex mean-zero weighted Hilbert spaces

The closed complex subspace has the inherited original weighted norm.
The projection deletes only the zero Fourier coefficient.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS

/-- Literal complex mean-zero sequences in their raw weighted Hilbert norm. -/
def complexMeanZeroWeightedSubmodule (w : Weight) : Submodule ℂ (WeightedCoeff w 2) :=
  (WeightedCoeff.evalCLM w 2 0).ker

@[simp] theorem mem_complexMeanZeroWeightedSubmodule (w : Weight) (q : WeightedCoeff w 2) :
    q ∈ complexMeanZeroWeightedSubmodule w ↔ q.val 0 = 0 := Iff.rfl

/-- Bounded literal zero-mode deletion, with values in the complex kernel. -/
def complexMeanZeroWeightedProjection (w : Weight) :
    WeightedCoeff w 2 →L[ℂ] complexMeanZeroWeightedSubmodule w :=
  ((WeightedCoeff.meanZeroWeightedLiftCLM w).comp
    (WeightedCoeff.meanZeroWeightedProjectionCLM w)).codRestrict _
    (fun _ => WeightedCoeff.meanZeroWeightedLift_zero w _)

theorem complexMeanZeroWeightedProjection_eq_self (w : Weight)
    (q : complexMeanZeroWeightedSubmodule w) :
    complexMeanZeroWeightedProjection w q.val = q :=
  Subtype.ext (WeightedCoeff.meanZeroWeightedLift_projection w q.val q.property)

theorem complexMeanZeroWeightedProjection_apply_other (w : Weight)
    (q : WeightedCoeff w 2) (n : ℤ) (hn : n ≠ 0) :
    (complexMeanZeroWeightedProjection w q).val.val n = q.val n := by
  change Coeff.deleteCoordinate 0 ((WeightedCoeff.weightEquiv w 2) q) n / _ = _
  rw [Coeff.deleteCoordinate_apply_other 0 n hn,WeightedCoeff.weightEquiv_apply]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero w n)

/-- The actual real mean-zero space embeds without changing coefficients. -/
def physicalRealToComplexMeanZeroWeighted (w : Weight) :
    physicalRealMeanZeroWeightedSubmodule w →L[ℝ] complexMeanZeroWeightedSubmodule w :=
  ((physicalRealMeanZeroWeightedSubmodule w).subtypeL).codRestrict
    ((complexMeanZeroWeightedSubmodule w).restrictScalars ℝ) (fun q => q.property.2)

@[simp] theorem physicalRealToComplexMeanZeroWeighted_val (w : Weight)
    (q : physicalRealMeanZeroWeightedSubmodule w) :
    (physicalRealToComplexMeanZeroWeighted w q).val = q.val := rfl

/-- Coefficient-preserving inclusion between the original complex native spaces. -/
def complexMeanZeroSobolevInclusion {s t : ℝ} (h : t ≤ s) :
    complexMeanZeroWeightedSubmodule (Weight.sobolev s) →L[ℂ]
      complexMeanZeroWeightedSubmodule (Weight.sobolev t) :=
  ((WeightedCoeff.sobolevInclusion h).comp
    (complexMeanZeroWeightedSubmodule (Weight.sobolev s)).subtypeL).codRestrict _
    (fun q => by
      change (WeightedCoeff.sobolevInclusion h q.val).val 0 = 0
      rw [WeightedCoeff.sobolevInclusion_apply]
      exact q.property)

@[simp] theorem complexMeanZeroSobolevInclusion_val {s t : ℝ} (h : t ≤ s)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    (complexMeanZeroSobolevInclusion h q).val = WeightedCoeff.sobolevInclusion h q.val := rfl

/-- The raw real native inclusion, expressed in the complex mean-zero space. -/
def physicalRealMeanZeroSobolevToComplex {s t : ℝ} (h : t ≤ s) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) →L[ℝ]
      complexMeanZeroWeightedSubmodule (Weight.sobolev t) :=
  (complexMeanZeroSobolevInclusion h).restrictScalars ℝ |>.comp
    (physicalRealToComplexMeanZeroWeighted (Weight.sobolev s))

@[simp] theorem physicalRealMeanZeroSobolevToComplex_val {s t : ℝ} (h : t ≤ s)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    (physicalRealMeanZeroSobolevToComplex h q).val = WeightedCoeff.sobolevInclusion h q.val := rfl

end NLS
