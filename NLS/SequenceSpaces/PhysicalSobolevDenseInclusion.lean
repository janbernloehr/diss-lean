import NLS.SequenceSpaces.PhysicalRealCoefficients
import NLS.SequenceSpaces.SobolevDerivative

/-! # Dense coefficient-preserving inclusions of physical real Sobolev spaces -/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

/-- The inclusion retains the physical conjugate-reflected real form. -/
def physicalSobolevInclusion {s t : ℝ} (h : t ≤ s) :
    physicalRealSubmodule (Weight.sobolev s) 2 →L[ℝ] physicalRealSubmodule (Weight.sobolev t) 2 :=
  (((sobolevInclusion (p := 2) h).restrictScalars ℝ).comp
    (physicalRealSubmodule (Weight.sobolev s) 2).subtypeL).codRestrict
      (physicalRealSubmodule (Weight.sobolev t) 2) (by
        intro a j
        change (sobolevInclusion h a.val).val j = conj ((sobolevInclusion h a.val).val (-j))
        simpa only [sobolevInclusion_apply] using! a.property j)

@[simp] theorem physicalSobolevInclusion_apply {s t : ℝ} (h : t ≤ s)
    (a : physicalRealSubmodule (Weight.sobolev s) 2) (j : ℤ) :
    (physicalSobolevInclusion h a).val.val j = a.val.val j := sobolevInclusion_apply h a.val j

theorem physicalSobolevInclusion_denseRange {s t : ℝ} (h : t ≤ s) :
    DenseRange (physicalSobolevInclusion h) := by
  have hI : DenseRange (sobolevInclusion (p := 2) h) := by
    intro a
    apply closure_mono (s := range (ofFinsupp (Weight.sobolev t) 2)) ?_
      (denseRange_ofFinsupp (Weight.sobolev t) 2 (by simp) a)
    rintro _ ⟨b,rfl⟩
    refine ⟨ofFinsupp (Weight.sobolev s) 2 b,?_⟩
    apply Subtype.ext
    funext j
    simp only [sobolevInclusion_apply,ofFinsupp_apply]
  let P := physicalRealPart (p := 2) (Weight.sobolev t) (Weight.sobolev_neg t)
  have hP : Function.Surjective P := fun a => ⟨a.val,physicalRealPart_real _ _ a⟩
  have hcomp := hP.denseRange.comp hI P.continuous
  intro a
  apply closure_mono (s := range (fun b => P (sobolevInclusion h b))) ?_ (hcomp a)
  rintro _ ⟨b,rfl⟩
  refine ⟨physicalRealPart (Weight.sobolev s) (Weight.sobolev_neg s) b,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext j
  simp only [physicalSobolevInclusion_apply,physicalRealPart_apply,sobolevInclusion_apply,P]

end NLS.WeightedCoeff
