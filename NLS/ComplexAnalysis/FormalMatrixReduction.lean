import NLS.ComplexAnalysis.MatrixTaylorEquivalence
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases

/-!
# Diagonal reduction of two-by-two formal matrices

A least-valuation entry divides every entry. Permutations put it in the
upper-left corner, and unit triangular operations eliminate its row and column.
No inverse of this possibly vanishing pivot is used.
-/

noncomputable section
open Complex PowerSeries Matrix
namespace NLS.ComplexAnalysis

/-- Every two-by-two formal matrix has an entry dividing all its entries. -/
theorem exists_formalMatrix_dividing_entry (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    ∃ i j, ∀ k l, A i j ∣ A k l := by
  obtain ⟨⟨i,j⟩, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin 2 × Fin 2))
    (fun ij => IsDiscreteValuationRing.addVal (PowerSeries ℂ) (A ij.1 ij.2))
    Finset.univ_nonempty
  exact ⟨i,j,fun k l => IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    (hmin (k,l) (Finset.mem_univ _))⟩

/-- The permutation matrix exchanging the two coordinates. -/
def formalSwapMatrix : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) := !![0,1;1,0]

/-- Exchanging two coordinates is an invertible formal operation. -/
theorem isUnit_formalSwapMatrix : IsUnit formalSwapMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [formalSwapMatrix, Matrix.det_fin_two_of]

/-- Row and column permutations move a dividing entry into the upper-left corner. -/
theorem exists_formalMatrix_dividing_pivot (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    ∃ L R : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ),
      IsUnit L ∧ IsUnit R ∧ ∀ i j, (L*A*R) 0 0 ∣ (L*A*R) i j := by
  obtain ⟨i,j,h⟩ := exists_formalMatrix_dividing_entry A
  fin_cases i <;> fin_cases j
  · exact ⟨1,1,isUnit_one,isUnit_one,by simpa using h⟩
  · refine ⟨1,formalSwapMatrix,isUnit_one,isUnit_formalSwapMatrix,?_⟩
    intro k l
    fin_cases k <;> fin_cases l
    · simp [formalSwapMatrix, Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 0 0
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 1 1
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 1 0
  · refine ⟨formalSwapMatrix,1,isUnit_formalSwapMatrix,isUnit_one,?_⟩
    intro k l
    fin_cases k <;> fin_cases l
    · simp [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 1 1
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 0 0
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 0 1
  · refine ⟨formalSwapMatrix,formalSwapMatrix,isUnit_formalSwapMatrix,isUnit_formalSwapMatrix,?_⟩
    intro k l
    fin_cases k <;> fin_cases l
    · simp [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 1 0
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 0 1
    · simpa [formalSwapMatrix, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h 0 0

/-- A dividing pivot permits diagonal elimination using only unit triangular matrices. -/
theorem formalMatrix_diagonalize_pivot (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (h01 : A 0 0 ∣ A 0 1) (h10 : A 0 0 ∣ A 1 0) :
    ∃ L R : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ),
      IsUnit L ∧ IsUnit R ∧ ∃ d, L*A*R = !![A 0 0,0;0,d] := by
  obtain ⟨b,hb⟩ := h01
  obtain ⟨c,hc⟩ := h10
  refine ⟨!![1,0;-c,1],!![1,-b;0,1],?_,?_,A 1 1-A 0 0*c*b,?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [Matrix.det_fin_two_of]
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [Matrix.det_fin_two_of]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hb,hc] <;> ring

/-- Every two-by-two complex formal matrix is equivalent by units to a diagonal matrix. -/
theorem exists_formalMatrix_diagonal_reduction (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) :
    ∃ L R : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ),
      IsUnit L ∧ IsUnit R ∧ ∃ f g, L*A*R = !![f,0;0,g] := by
  obtain ⟨L,R,hL,hR,h⟩ := exists_formalMatrix_dividing_pivot A
  obtain ⟨L',R',hL',hR',d,hd⟩ := formalMatrix_diagonalize_pivot (L*A*R) (h 0 1) (h 1 0)
  exact ⟨L'*L,R*R',hL'.mul hL,hR.mul hR',(L*A*R) 0 0,d,by simpa only [mul_assoc] using hd⟩

end NLS.ComplexAnalysis
