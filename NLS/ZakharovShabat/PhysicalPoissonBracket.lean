import NLS.ZakharovShabat.PhysicalCotangentGradient
import NLS.Poisson.SourceCoordinateBrackets

/-! # Poisson brackets on the physical Hilbert space

The bracket uses actual complex differentials and their unique physical
L2 gradients. The chain rule identifies it with the source bracket. Actual
physical Fourier integrals check the minus i sign and opposite-frequency
pairing independently of the Birkhoff coordinates.
-/

noncomputable section
open Set MeasureTheory Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
open NLS.Poisson NLS.Fourier

/-- The physical bracket uses the actual complex differentials at the original physical source. -/
def physicalBracket (F G : IntervalPairL2 → ℂ) (u : IntervalPairL2) : ℂ :=
  physicalCotangentBivector (fderiv ℂ F u) (fderiv ℂ G u)

/-- Physical brackets pull back to the source bracket under the exact Fourier map. -/
theorem physicalBracket_eq_source (F G : IntervalPairL2 → ℂ) (u : IntervalPairL2)
    (hF : DifferentiableAt ℂ F u) (hG : DifferentiableAt ℂ G u) :
    physicalBracket F G u = sourceBracket le_rfl (F ∘ sourcePhysicalL2)
      (G ∘ sourcePhysicalL2) (sourcePhysicalL2Equiv.symm u) := by
  have hder (H : IntervalPairL2 → ℂ) (hH : DifferentiableAt ℂ H u) :
      fderiv ℂ (H ∘ sourcePhysicalL2) (sourcePhysicalL2Equiv.symm u) =
        (fderiv ℂ H u).comp sourcePhysicalL2 := by
    have hh' : HasFDerivAt H (fderiv ℂ H u)
        (sourcePhysicalL2 (sourcePhysicalL2Equiv.symm u)) := by
      simpa only [sourcePhysicalL2_equiv_symm] using hH.hasFDerivAt
    have hd := hh'.comp (sourcePhysicalL2Equiv.symm u)
      (sourcePhysicalL2.hasFDerivAt (x := sourcePhysicalL2Equiv.symm u))
    simpa only [sourcePhysicalL2_equiv_symm] using hd.fderiv
  rw [physicalBracket,physicalCotangentBivector_eq_source,sourceBracket,hder F hF,hder G hG]

/-- The actual physical Fourier integrals pair at opposite frequencies with factor minus i. -/
theorem physicalBracket_fourier (n m : ℤ) (u : IntervalPairL2) :
    physicalBracket (fun v => intervalFourierCoefficient 1 v.ofLp.1 n)
      (fun v => intervalFourierCoefficient 1 v.ofLp.2 m) u = if n = -m then -I else 0 := by
  have hx : (fun v : IntervalPairL2 => intervalFourierCoefficient 1 v.ofLp.1 n) =
      sourceCoordinateLeft n ∘ sourcePhysicalL2Equiv.symm := by
    funext v
    exact (sourcePhysicalL2Equiv_symm_fst v n).symm
  have hy : (fun v : IntervalPairL2 => intervalFourierCoefficient 1 v.ofLp.2 m) =
      sourceCoordinateRight m ∘ sourcePhysicalL2Equiv.symm := by
    funext v
    exact (sourcePhysicalL2Equiv_symm_snd v m).symm
  rw [hx,hy]
  have hdx : DifferentiableAt ℂ (sourceCoordinateLeft n ∘ sourcePhysicalL2Equiv.symm) u :=
    (sourceCoordinateLeft (p := 2) n).differentiableAt.comp u sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.differentiableAt
  have hdy : DifferentiableAt ℂ (sourceCoordinateRight m ∘ sourcePhysicalL2Equiv.symm) u :=
    (sourceCoordinateRight (p := 2) m).differentiableAt.comp u sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.differentiableAt
  rw [physicalBracket_eq_source _ _ _ hdx hdy]
  have hleft : (sourceCoordinateLeft n ∘ sourcePhysicalL2Equiv.symm) ∘ sourcePhysicalL2 =
      sourceCoordinateLeft (p := 2) n := by
    funext φ
    simp only [Function.comp_apply,← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply]
  have hright : (sourceCoordinateRight m ∘ sourcePhysicalL2Equiv.symm) ∘ sourcePhysicalL2 =
      sourceCoordinateRight (p := 2) m := by
    funext φ
    simp only [Function.comp_apply,← sourcePhysicalL2Equiv_apply,LinearIsometryEquiv.symm_apply_apply]
  rw [hleft,hright]
  exact sourceBracket_coordinateLeft_coordinateRight le_rfl n m _

/-- The physical bracket is antisymmetric, directly from its literal integral form. -/
theorem physicalBracket_antisymm (F G : IntervalPairL2 → ℂ) (u : IntervalPairL2) :
    physicalBracket F G u = -physicalBracket G F u := by
  simp only [physicalBracket,physicalCotangentBivector_eq_source]
  exact sourceBivector_antisymm le_rfl _ _

/-- Every physical functional has zero bracket with itself. -/
@[simp] theorem physicalBracket_self (F : IntervalPairL2 → ℂ) (u : IntervalPairL2) :
    physicalBracket F F u = 0 := by
  rw [physicalBracket,physicalCotangentBivector_eq_source]
  exact sourceBivector_self le_rfl _

end NLS.ZakharovShabat
