import NLS.ComplexAnalysis.BanachFiniteJets
import NLS.ComplexAnalysis.MatrixTaylorDeterminant
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant

/-! # Actual analytic two-mode action and formal matrix Taylor kernels -/
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace NLS.ComplexAnalysis
open NLS.FunctionalAnalysis

/-- The matrix of an actual two-mode operator in the original pair coordinates. -/
def pairOperatorMatrixCLM : ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  ({ toFun := fun T => !![(T (1,0)).1,(T (0,1)).1;(T (1,0)).2,(T (0,1)).2]
     map_add' := by intro T S; ext i j; fin_cases i <;> fin_cases j <;> rfl
     map_smul' := by intro c T; ext i j; fin_cases i <;> fin_cases j <;> rfl } :
    ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ).toContinuousLinearMap

/-- The original pair-valued action of a two-by-two matrix. -/
def matrixPairAction (A : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) : ℂ × ℂ :=
  (A 0 0*v.1+A 0 1*v.2,A 1 0*v.1+A 1 1*v.2)

/-- Matrix conversion preserves the full actual operator action. -/
theorem matrixPairAction_pairOperator (T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (v : ℂ × ℂ) :
    matrixPairAction (pairOperatorMatrixCLM T) v = T v := by
  have he : T v = v.1 • T (1,0)+v.2 • T (0,1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Prod.ext <;> simp
  rw [he]
  apply Prod.ext <;> change _ = v.1 * _ + v.2 * _ <;>
    dsimp [matrixPairAction, pairOperatorMatrixCLM] <;> ring

/-- The converted matrix has exactly the actual two-mode determinant. -/
theorem det_pairOperatorMatrix (T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :
    (pairOperatorMatrixCLM T).det = T.toLinearMap.det := by
  rw [Matrix.det_fin_two, NLS.FiniteSpectralDeterminant.det_prod_formula]
  rfl

/-- Formal Taylor multiplication is precisely the normalized finite jet of
the actual analytic matrix acting on the actual amplitude polynomial. -/
theorem matrixTaylorJetMap_eq_analyticFiniteJet
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)}
    (hA : HasFPowerSeriesAt A p 0) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    matrixTaylorJetMap (matrixFormalTaylor p) N v =
      analyticFiniteJet N (fun t => matrixPairAction (A t) (pencilChainPolynomial N v t)) := by
  have h00 := hasFPowerSeriesAt_matrixEntry hA 0 0
  have h01 := hasFPowerSeriesAt_matrixEntry hA 0 1
  have h10 := hasFPowerSeriesAt_matrixEntry hA 1 0
  have h11 := hasFPowerSeriesAt_matrixEntry hA 1 1
  let v0 := fun j : Fin N => (v j).1
  let v1 := fun j : Fin N => (v j).2
  have hp0 := analyticAt_chainPolynomial N v0 0
  have hp1 := analyticAt_chainPolynomial N v1 0
  have hrow0 := (h00.analyticAt.mul hp0).add (h01.analyticAt.mul hp1)
  have hrow1 := (h10.analyticAt.mul hp0).add (h11.analyticAt.mul hp1)
  have hpoly0 (t : ℂ) : (pencilChainPolynomial N v t).1 = pencilChainPolynomial N v0 t :=
    chainPolynomial_compCLM (ContinuousLinearMap.fst ℂ ℂ ℂ) N v t
  have hpoly1 (t : ℂ) : (pencilChainPolynomial N v t).2 = pencilChainPolynomial N v1 t :=
    chainPolynomial_compCLM (ContinuousLinearMap.snd ℂ ℂ ℂ) N v t
  have he : (fun t => matrixPairAction (A t) (pencilChainPolynomial N v t)) =
      (fun t => (A t 0 0*pencilChainPolynomial N v0 t+A t 0 1*pencilChainPolynomial N v1 t,
        A t 1 0*pencilChainPolynomial N v0 t+A t 1 1*pencilChainPolynomial N v1 t)) := by
    funext t
    simp only [matrixPairAction, hpoly0, hpoly1]
  have hj := analyticFiniteJet_prod hrow0 hrow1 N
  simp only [Pi.add_def, Pi.mul_def] at hj
  have hj0 := analyticFiniteJet_add (h00.analyticAt.mul hp0) (h01.analyticAt.mul hp1) N
  have hj1 := analyticFiniteJet_add (h10.analyticAt.mul hp0) (h11.analyticAt.mul hp1) N
  simp only [Pi.mul_def] at hj0 hj1
  rw [analyticFiniteJet_scalarProduct h00, analyticFiniteJet_scalarProduct h01] at hj0
  rw [analyticFiniteJet_scalarProduct h10, analyticFiniteJet_scalarProduct h11] at hj1
  rw [he, hj, hj0, hj1]
  rfl

/-- The formal matrix Taylor kernel is exactly vanishing of the retained
derivatives of the actual matrix residual, with the same finite coefficients. -/
theorem mem_matrixTaylorKernel_iff_derivatives
    {A : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)}
    (hA : HasFPowerSeriesAt A p 0) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    v ∈ LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) ↔
      ∀ k : Fin N, iteratedDeriv k.val
        (fun t => matrixPairAction (A t) (pencilChainPolynomial N v t)) 0 = 0 := by
  rw [LinearMap.mem_ker, matrixTaylorJetMap_eq_analyticFiniteJet hA, analyticFiniteJet_eq_zero_iff]

/-- The formal matrix kernel criterion applies directly to a genuine analytic
two-mode operator family, without changing its pair coordinates. -/
theorem mem_pairOperatorTaylorKernel_iff_derivatives
    (B : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    {p : FormalMultilinearSeries ℂ ℂ (Matrix (Fin 2) (Fin 2) ℂ)}
    (hB : HasFPowerSeriesAt (fun t => pairOperatorMatrixCLM (B t)) p 0)
    (N : ℕ) (v : Fin N → ℂ × ℂ) :
    v ∈ LinearMap.ker (matrixTaylorJetMap (matrixFormalTaylor p) N) ↔
      ∀ k : Fin N, iteratedDeriv k.val (fun t => B t (pencilChainPolynomial N v t)) 0 = 0 := by
  simpa only [matrixPairAction_pairOperator] using mem_matrixTaylorKernel_iff_derivatives hB N v

end NLS.ComplexAnalysis
