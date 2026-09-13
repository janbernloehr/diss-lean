import NLS.ComplexAnalysis.ScalarTaylorAlgebra
import NLS.ComplexAnalysis.MatrixTaylorNullity
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Determinants and convergent matrix Taylor series

Entrywise extraction of a convergent matrix series commutes with the
two-by-two determinant, so its formal determinant order equals the analytic
vanishing order of the actual determinant.
-/

noncomputable section
open Complex PowerSeries Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ComplexAnalysis

/-- Continuous extraction of one entry of a two-by-two complex matrix. -/
def matrixEntryCLM (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ →L[ℂ] ℂ :=
  ({ toFun := fun A => A i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

/-- The scalar multilinear series in one matrix entry. -/
def matrixEntryTaylor (p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ))
    (i j : Fin 2) : FormalMultilinearSeries ℂ ℂ ℂ := (matrixEntryCLM i j).compFormalMultilinearSeries p

/-- The formal power-series matrix obtained from the ordinary matrix Taylor coefficients. -/
def matrixFormalTaylor (p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)) :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) := fun i j => scalarFormalTaylor (matrixEntryTaylor p i j)

/-- Entrywise formal extraction retains exactly the given ordinary coefficients. -/
@[simp] theorem coeff_matrixFormalTaylor
    (p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)) (i j : Fin 2) (n : ℕ) :
    PowerSeries.coeff n (matrixFormalTaylor p i j) = p n (fun _ => 1) i j := by
  rw [matrixFormalTaylor,coeff_scalarFormalTaylor]
  rfl

/-- Every extracted entry series converges to the corresponding analytic matrix entry. -/
theorem hasFPowerSeriesAt_matrixEntry {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (i j : Fin 2) :
    HasFPowerSeriesAt (fun w => f w i j) (matrixEntryTaylor p i j) z := by
  obtain ⟨r,hr⟩ := hf
  exact ⟨r,(matrixEntryCLM i j).comp_hasFPowerSeriesOnBall hr⟩

/-- The determinant has a convergent scalar Taylor series whose formal extraction is the formal determinant. -/
theorem exists_hasFPowerSeriesAt_det_matrixFormalTaylor {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) : ∃ s : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesAt (fun w => (f w).det) s z ∧ scalarFormalTaylor s = (matrixFormalTaylor p).det := by
  have h00 := hasFPowerSeriesAt_matrixEntry hf 0 0
  have h01 := hasFPowerSeriesAt_matrixEntry hf 0 1
  have h10 := hasFPowerSeriesAt_matrixEntry hf 1 0
  have h11 := hasFPowerSeriesAt_matrixEntry hf 1 1
  obtain ⟨u,hu⟩ := h00.analyticAt.mul h11.analyticAt
  obtain ⟨v,hv⟩ := h01.analyticAt.mul h10.analyticAt
  refine ⟨u-v,?_,?_⟩
  · simpa only [Matrix.det_fin_two] using! hu.sub hv
  · rw [scalarFormalTaylor_sub,scalarFormalTaylor_mul h00 h11 hu,scalarFormalTaylor_mul h01 h10 hv,Matrix.det_fin_two]
    rfl

/-- The formal determinant and the actual analytic determinant have exactly the same vanishing order. -/
theorem order_det_matrixFormalTaylor {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) :
    (matrixFormalTaylor p).det.order = analyticOrderAt (fun w => (f w).det) z := by
  obtain ⟨s,hs,he⟩ := exists_hasFPowerSeriesAt_det_matrixFormalTaylor hf
  rw [← he]
  exact order_scalarFormalTaylor hs

/-- For a finite-order analytic determinant, the matrix Taylor nullities eventually recover that order. -/
theorem eventually_matrixTaylorNullity_eq_analytic_det_order {f : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (hdet : analyticOrderAt (fun w => (f w).det) z ≠ ⊤) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N)) : ℕ∞) =
        analyticOrderAt (fun w => (f w).det) z := by
  rw [← order_det_matrixFormalTaylor hf] at hdet ⊢
  exact eventually_finrank_matrixTaylorKernel_eq_det_order _ (fun h => hdet (by simp [h]))

end NLS.ComplexAnalysis
