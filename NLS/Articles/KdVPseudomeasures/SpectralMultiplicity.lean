import NLS.Articles.KdVPseudomeasures.SpectralResolvent
import NLS.KdV.PseudomeasureRootSpaces

/-! # Physical algebraic multiplicity for the original source potentials

Multiplicity is the dimension of the full root space of the actual original
H-minus-one partial operator, with every repeated application in its unchanged
H1 domain. This dimension is proved finite and equal to that of any actual
compact resolvent at the transformed spectral value. Equality with the analytic
order of the two-mode determinant is still a separate obligation.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The original full physical algebraic root space is finite dimensional. -/
theorem finiteDimensional_sourceHillRootSpaceTop (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    FiniteDimensional ℂ (NLS.KdV.singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z) := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact NLS.KdV.finiteDimensional_endpointHillRootSpaceTop r hr.1 hr.2 (sourceEndpointCoefficients r q) z

/-- The actual source algebraic root chains stabilize after finitely many domain-preserving steps. -/
theorem sourceHillRootSpace_stabilizes (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      NLS.KdV.singularHillRootSpace (sourceComplexHminusOne r hr q) z n =
        NLS.KdV.singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact NLS.KdV.endpointHillRootSpace_stabilizes r hr.1 hr.2 (sourceEndpointCoefficients r q) z

/-- Finite algebraic multiplicity defined directly from the original physical operator's full root space. -/
def sourceHillAlgebraicMultiplicity (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) : ℕ :=
  letI := finiteDimensional_sourceHillRootSpaceTop r hr q z
  Module.finrank ℂ (NLS.KdV.singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z)

/-- No algebraic multiplicity is changed by the exact original Fourier realization. -/
theorem sourceHillAlgebraicMultiplicity_eq (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    sourceHillAlgebraicMultiplicity r hr q z =
      NLS.KdV.endpointHillAlgebraicMultiplicity r hr.1 hr.2 (sourceEndpointCoefficients r q) z := by
  unfold sourceHillAlgebraicMultiplicity NLS.KdV.endpointHillAlgebraicMultiplicity
  rw [sourceEndpointCoefficients_HminusOne_complex]

/-- The actual original algebraic multiplicity is positive exactly on the actual source spectrum. -/
theorem sourceHillAlgebraicMultiplicity_pos_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    0 < sourceHillAlgebraicMultiplicity r hr q z ↔ z ∈ sourceHillSpectrum r hr q := by
  rw [sourceHillAlgebraicMultiplicity_eq, sourceHillSpectrum_eq]
  exact NLS.KdV.endpointHillAlgebraicMultiplicity_pos_iff r hr.1 hr.2 (sourceEndpointCoefficients r q) z

/-- Every finite original physical chain level equals the corresponding actual compact-resolvent generalized eigenspace. -/
theorem sourceHillRootSpace_eq_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (a z : ℂ)
    (ha : a ∉ sourceHillSpectrum r hr q) (hza : z ≠ a) (n : ℕ) :
    NLS.KdV.singularHillRootSpace (sourceComplexHminusOne r hr q) z n =
      Module.End.genEigenspace
        (NLS.KdV.endpointHillBaseResolvent r hr.2 (sourceEndpointCoefficients r q) a).toLinearMap (z-a)⁻¹ n := by
  have hres : a ∈ NLS.KdV.endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) := by
    rw [sourceHillSpectrum_eq] at ha
    exact not_not.mp ha
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact NLS.KdV.endpointHillRootSpace_eq_resolvent r hr.2 (sourceEndpointCoefficients r q) a z hres hza n

/-- Actual source algebraic multiplicity equals compact-resolvent algebraic multiplicity for any resolvent point. -/
theorem sourceHillAlgebraicMultiplicity_eq_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (a z : ℂ)
    (ha : a ∉ sourceHillSpectrum r hr q) (hza : z ≠ a) :
    sourceHillAlgebraicMultiplicity r hr q z = Module.finrank ℂ
      (Module.End.genEigenspace
        (NLS.KdV.endpointHillBaseResolvent r hr.2 (sourceEndpointCoefficients r q) a).toLinearMap (z-a)⁻¹ ⊤) := by
  have hres : a ∈ NLS.KdV.endpointHillResolventSet r hr.2 (sourceEndpointCoefficients r q) := by
    rw [sourceHillSpectrum_eq] at ha
    exact not_not.mp ha
  rw [sourceHillAlgebraicMultiplicity_eq]
  exact NLS.KdV.endpointHillAlgebraicMultiplicity_eq_resolvent r hr.1 hr.2
    (sourceEndpointCoefficients r q) a z hres hza

/-- Every actual original physical generalized eigenvector has the improved source endpoint regularity. -/
theorem sourceHillRootSpaceTop_regular (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ)
    (x : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hx : x ∈ NLS.KdV.singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z) :
    ∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = x.val := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q] at hx
  exact NLS.KdV.endpointHillRootSpaceTop_regular r hr.1 hr.2 (sourceEndpointCoefficients r q) z x hx

end NLS.Articles.KdVPseudomeasures
