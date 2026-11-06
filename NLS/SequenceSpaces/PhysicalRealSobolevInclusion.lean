import NLS.SequenceSpaces.PhysicalRealDeletedHilbert
import NLS.SequenceSpaces.MeanZeroSobolevIdentities

/-! # Literal Sobolev inclusions on the physical real normalized space -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
namespace NLS

/-- The exact native normalized inclusion preserves physical Fourier
reality at EVERY pair of eligible real Sobolev orders. -/
theorem meanZeroSobolevInclusion_physical_real {s t : ℝ} (h : t≤s)
    (a : physicalRealDeletedSubmodule) :
    deletedL2Conjugation (WeightedCoeff.meanZeroSobolevInclusion h a.val)=
      WeightedCoeff.meanZeroSobolevInclusion h a.val := by
  have hr := (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg s) a.val).mpr a.property
  have he (j : ℤ) :
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev t)
        (WeightedCoeff.meanZeroSobolevInclusion h a.val)).val j=
      (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s) a.val).val j := by
    have hc := congrArg (fun q : WeightedCoeff (Weight.sobolev t) 2 => q.val j)
      (WeightedCoeff.meanZeroSobolevInclusion_lift h a.val)
    exact hc.trans (WeightedCoeff.sobolevInclusion_apply h _ j)
  apply (WeightedCoeff.meanZeroWeightedLift_real_iff _ (Weight.sobolev_neg t) _).mp
  intro j
  exact (he (-j)).trans ((hr j).trans (congrArg conj (he j).symm))

/-- The SAME physical real Hilbert type carries each native weighted
norm through its literal charts; this is the actual native inclusion. -/
def physicalRealSobolevInclusion {s t : ℝ} (h : t≤s) :
    physicalRealDeletedSubmodule →L[ℝ] physicalRealDeletedSubmodule :=
  (((WeightedCoeff.meanZeroSobolevInclusion h).restrictScalars ℝ).comp
    physicalRealDeletedSubmodule.subtypeL).codRestrict physicalRealDeletedSubmodule
      (meanZeroSobolevInclusion_physical_real h)

@[simp] theorem physicalRealSobolevInclusion_val {s t : ℝ} (h : t≤s)
    (a : physicalRealDeletedSubmodule) :
    (physicalRealSobolevInclusion h a).val=WeightedCoeff.meanZeroSobolevInclusion h a.val := rfl

theorem physicalRealSobolevInclusion_injective {s t : ℝ} (h : t≤s) :
    Function.Injective (physicalRealSobolevInclusion h) := by
  intro a b he
  exact Subtype.ext (WeightedCoeff.meanZeroSobolevInclusion_injective h (congrArg Subtype.val he))

@[simp] theorem physicalRealSobolevInclusion_self (s : ℝ) (h : s≤s)
    (a : physicalRealDeletedSubmodule) : physicalRealSobolevInclusion h a=a := by
  apply Subtype.ext
  rw [physicalRealSobolevInclusion_val,WeightedCoeff.meanZeroSobolevInclusion_self]
  rfl

end NLS
