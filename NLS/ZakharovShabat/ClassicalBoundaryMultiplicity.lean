import NLS.ZakharovShabat.BoundaryFormalDeterminantOrder
import NLS.ComplexAnalysis.MatrixTaylorDeterminant

/-!
# Analytic boundary determinant orders and original multiplicities

The convergent boundary matrix Taylor series has the previously constructed
formal matrix. Its determinant therefore has analytic vanishing order equal
to the original parity algebraic multiplicity.
-/

noncomputable section
open Set Complex Matrix MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The actual formal boundary matrix is entrywise extraction of its convergent Taylor series. -/
theorem classicalBoundaryFormalMatrix_eq_matrixFormalTaylor (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    classicalBoundaryFormalMatrix Φ z σ = matrixFormalTaylor (classicalBoundarySeries Φ z σ) := by
  apply Matrix.ext
  intro i j
  ext n
  rw [coeff_classicalBoundaryFormalMatrix,coeff_matrixFormalTaylor]

/-- Every boundary determinant has a convergent scalar Taylor series equal formally to the boundary determinant. -/
theorem exists_classicalBoundaryDeterminant_taylor (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun w => (classicalMonodromy Φ w-σ • 1).det) s z ∧
      scalarFormalTaylor s = (classicalBoundaryFormalMatrix Φ z σ).det := by
  rw [classicalBoundaryFormalMatrix_eq_matrixFormalTaylor]
  exact exists_hasFPowerSeriesAt_det_matrixFormalTaylor
    (hasFPowerSeriesOnBall_classicalBoundaryMatrix Φ z σ).hasFPowerSeriesAt

/-- Formal and analytic characteristic determinant orders agree for every continuous potential and multiplier. -/
theorem order_classicalBoundaryFormalMatrix_det_eq_analyticOrder (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    (classicalBoundaryFormalMatrix Φ z σ).det.order =
      analyticOrderAt (fun w => (classicalMonodromy Φ w-σ • 1).det) z := by
  rw [classicalBoundaryFormalMatrix_eq_matrixFormalTaylor]
  exact order_det_matrixFormalTaylor
    (hasFPowerSeriesOnBall_classicalBoundaryMatrix Φ z σ).hasFPowerSeriesAt

/-- The classical analytic parity determinant has precisely the original parity algebraic multiplicity. -/
theorem analyticOrderAt_classicalBoundaryDeterminant
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) :
    analyticOrderAt (fun w => (classicalMonodromy Φ w-wave r 1 • 1).det) z =
      (parityAlgebraicMultiplicity (by simp) φ r z : ℕ∞) := by
  rw [← order_classicalBoundaryFormalMatrix_det_eq_analyticOrder]
  exact order_classicalBoundaryFormalMatrix_det φ hφ Φ hΦ z r

/-- The classical parity determinant has finite analytic order at every spectral parameter. -/
theorem analyticOrderAt_classicalBoundaryDeterminant_ne_top
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) :
    analyticOrderAt (fun w => (classicalMonodromy Φ w-wave r 1 • 1).det) z ≠ ⊤ := by
  rw [analyticOrderAt_classicalBoundaryDeterminant φ hφ Φ hΦ]
  exact ENat.natCast_ne_top _

/-- The actual finite boundary nullity sequence stabilizes at the analytic determinant order. -/
theorem eventually_boundaryJetNullity_eq_analytic_det_order
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) : ∀ᶠ N : ℕ in Filter.atTop,
      (boundaryJetNullity Φ z (wave r 1) N : ℕ∞) =
        analyticOrderAt (fun w => (classicalMonodromy Φ w-wave r 1 • 1).det) z := by
  simpa only [order_classicalBoundaryFormalMatrix_det_eq_analyticOrder] using
    eventually_boundaryJetNullity_eq_formal_det_order φ hφ Φ hΦ z r

end NLS.ZakharovShabat
