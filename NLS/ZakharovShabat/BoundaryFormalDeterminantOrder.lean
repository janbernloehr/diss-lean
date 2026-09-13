import NLS.ZakharovShabat.ClassicalBoundaryFormalJets
import NLS.ComplexAnalysis.MatrixTaylorNullity

/-!
# Formal boundary determinant order and original multiplicity

Bounded original root dimensions rule out a singular formal boundary matrix.
General formal reduction then identifies its determinant order with the
original parity algebraic multiplicity. Analytic determinant compatibility
is a separate remaining step.
-/

noncomputable section
open Set Complex Matrix MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The formal boundary determinant is nonzero because the original root dimensions are bounded. -/
theorem classicalBoundaryFormalMatrix_det_ne_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : (classicalBoundaryFormalMatrix Φ z (wave r 1)).det ≠ 0 := by
  apply det_ne_zero_of_bounded_matrixTaylorNullity _ (parityAlgebraicMultiplicity (by simp) φ r z)
  intro N
  rw [← boundaryJetNullity_eq_formalMatrixNullity]
  exact boundaryJetNullity_le_parityMultiplicity φ hφ Φ hΦ z r N

/-- The actual finite boundary nullities eventually recover their formal determinant order. -/
theorem eventually_boundaryJetNullity_eq_formal_det_order
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : ∀ᶠ N : ℕ in Filter.atTop,
      (boundaryJetNullity Φ z (wave r 1) N : ℕ∞) =
        (classicalBoundaryFormalMatrix Φ z (wave r 1)).det.order := by
  simpa only [boundaryJetNullity_eq_formalMatrixNullity] using
    eventually_finrank_matrixTaylorKernel_eq_det_order _
      (classicalBoundaryFormalMatrix_det_ne_zero φ hφ Φ hΦ z r)

/-- The original parity algebraic multiplicity is exactly the order of the formal boundary determinant. -/
theorem order_classicalBoundaryFormalMatrix_det
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : (classicalBoundaryFormalMatrix Φ z (wave r 1)).det.order =
      (parityAlgebraicMultiplicity (by simp) φ r z : ℕ∞) := by
  obtain ⟨N,hN,hM⟩ := ((eventually_boundaryJetNullity_eq_formal_det_order φ hφ Φ hΦ z r).and
    (eventually_boundaryJetNullity_eq_parityMultiplicity φ hφ Φ hΦ z r)).exists
  rw [← hN,hM]

end NLS.ZakharovShabat
