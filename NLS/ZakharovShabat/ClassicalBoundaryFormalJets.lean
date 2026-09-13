import NLS.ZakharovShabat.BoundaryJetMultiplicity
import NLS.ComplexAnalysis.MatrixTaylorJets

/-!
# Formal matrix representation of the actual boundary Taylor systems

The formal entries are the coefficients of the already constructed convergent
monodromy boundary series. Their truncated matrix multiplication is exactly
the original finite boundary map, so formal nullity calculations apply directly.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ComplexAnalysis
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The ordinary formal power-series matrix of the actual characteristic boundary matrix. -/
def classicalBoundaryFormalMatrix (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) :
    Matrix (Fin 2) (Fin 2) (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun n => classicalBoundarySeries Φ z σ n (fun _ => 1) i j)

/-- Every formal entry is taken from the corresponding actual convergent Taylor coefficient. -/
@[simp] theorem coeff_classicalBoundaryFormalMatrix (Φ : Curve (ℂ × ℂ)) (z σ : ℂ)
    (i j : Fin 2) (n : ℕ) : PowerSeries.coeff n (classicalBoundaryFormalMatrix Φ z σ i j) =
      classicalBoundarySeries Φ z σ n (fun _ => 1) i j := by
  simp [classicalBoundaryFormalMatrix]

/-- The original finite boundary Taylor map is precisely truncated multiplication by its formal matrix. -/
theorem finiteBoundaryJetMap_eq_matrixTaylorJetMap (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ) :
    finiteBoundaryJetMap Φ z σ N = matrixTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ) N := by
  apply LinearMap.ext
  intro v
  funext k
  apply Prod.ext
  · change (∑ j ∈ Finset.range (k.val+1), classicalMatrixAction (classicalBoundarySeries Φ z σ j (fun _ => 1))
        (initialJetExtension N v (k.val-j))).1 = _
    rw [Prod.fst_sum]
    change _ = scalarTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ 0 0) N (fun j => (v j).1) k +
      scalarTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ 0 1) N (fun j => (v j).2) k
    rw [scalarTaylorJetMap_apply_eq_sum,scalarTaylorJetMap_apply_eq_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hlt : k.val-j < N := (Nat.sub_le _ _).trans_lt k.isLt
    simp [classicalMatrixAction,initialJetExtension,hlt]
  · change (∑ j ∈ Finset.range (k.val+1), classicalMatrixAction (classicalBoundarySeries Φ z σ j (fun _ => 1))
        (initialJetExtension N v (k.val-j))).2 = _
    rw [Prod.snd_sum]
    change _ = scalarTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ 1 0) N (fun j => (v j).1) k +
      scalarTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ 1 1) N (fun j => (v j).2) k
    rw [scalarTaylorJetMap_apply_eq_sum,scalarTaylorJetMap_apply_eq_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hlt : k.val-j < N := (Nat.sub_le _ _).trans_lt k.isLt
    simp [classicalMatrixAction,initialJetExtension,hlt]

/-- Formal matrix nullity is exactly the previously defined actual boundary nullity at every length. -/
theorem boundaryJetNullity_eq_formalMatrixNullity (Φ : Curve (ℂ × ℂ)) (z σ : ℂ) (N : ℕ) :
    boundaryJetNullity Φ z σ N =
      Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap (classicalBoundaryFormalMatrix Φ z σ) N)) := by
  rw [boundaryJetNullity,finiteBoundaryJetMap_eq_matrixTaylorJetMap]

end NLS.ZakharovShabat
