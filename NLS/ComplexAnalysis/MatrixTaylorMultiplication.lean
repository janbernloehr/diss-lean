import NLS.ComplexAnalysis.MatrixTaylorJets

/-!
# Multiplicative finite matrix Taylor action

Formal matrix multiplication acts by composition on every finite Taylor space.
In particular an invertible formal row or column operation induces an invertible
linear transformation of the retained coefficient vectors.
-/

noncomputable section
open Complex PowerSeries Matrix
namespace NLS.ComplexAnalysis

/-- The first output coefficient vector is the first formal row acting by scalar convolution. -/
theorem matrixTaylorJetMap_fst (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    (fun k => (matrixTaylorJetMap A N v k).1) =
      scalarTaylorJetMap (A 0 0) N (fun j => (v j).1)+scalarTaylorJetMap (A 0 1) N (fun j => (v j).2) := rfl

/-- The second output coefficient vector is the second formal row acting by scalar convolution. -/
theorem matrixTaylorJetMap_snd (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    (fun k => (matrixTaylorJetMap A N v k).2) =
      scalarTaylorJetMap (A 1 0) N (fun j => (v j).1)+scalarTaylorJetMap (A 1 1) N (fun j => (v j).2) := rfl

/-- The identity formal matrix fixes every finite Taylor jet. -/
@[simp] theorem matrixTaylorJetMap_one (N : ℕ) : matrixTaylorJetMap 1 N = LinearMap.id := by
  apply LinearMap.ext
  intro v
  funext k
  change (scalarTaylorJetMap 1 N (fun j => (v j).1) k+scalarTaylorJetMap 0 N (fun j => (v j).2) k,
    scalarTaylorJetMap 0 N (fun j => (v j).1) k+scalarTaylorJetMap 1 N (fun j => (v j).2) k) = _
  simp only [scalarTaylorJetMap_one,scalarTaylorJetMap_zero,LinearMap.id_apply,LinearMap.zero_apply,Pi.zero_apply,zero_add,add_zero]

/-- Formal matrix products give exactly compositions of the finite Taylor actions. -/
theorem matrixTaylorJetMap_mul (A B : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (N : ℕ) :
    matrixTaylorJetMap (A*B) N = (matrixTaylorJetMap A N).comp (matrixTaylorJetMap B N) := by
  apply LinearMap.ext
  intro v
  have hf : (fun k => (matrixTaylorJetMap (A*B) N v k).1) =
      (fun k => (matrixTaylorJetMap A N (matrixTaylorJetMap B N v) k).1) := by
    rw [matrixTaylorJetMap_fst (A*B),matrixTaylorJetMap_fst A,matrixTaylorJetMap_fst B,matrixTaylorJetMap_snd B]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,scalarTaylorJetMap_add,scalarTaylorJetMap_mul,
      LinearMap.add_apply,LinearMap.comp_apply,map_add]
    abel
  have hs : (fun k => (matrixTaylorJetMap (A*B) N v k).2) =
      (fun k => (matrixTaylorJetMap A N (matrixTaylorJetMap B N v) k).2) := by
    rw [matrixTaylorJetMap_snd (A*B),matrixTaylorJetMap_snd A,matrixTaylorJetMap_fst B,matrixTaylorJetMap_snd B]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,scalarTaylorJetMap_add,scalarTaylorJetMap_mul,
      LinearMap.add_apply,LinearMap.comp_apply,map_add]
    abel
  funext k
  exact Prod.ext (congrFun hf k) (congrFun hs k)

/-- Invertible formal matrices act bijectively at every truncation length. -/
theorem matrixTaylorJetMap_bijective_of_isUnit (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ))
    (hA : IsUnit A) (N : ℕ) : Function.Bijective (matrixTaylorJetMap A N) := by
  obtain ⟨u,rfl⟩ := hA
  have hl : (matrixTaylorJetMap (↑u⁻¹) N).comp (matrixTaylorJetMap (↑u) N) = LinearMap.id := by
    rw [← matrixTaylorJetMap_mul,Units.inv_mul,matrixTaylorJetMap_one]
  have hr : (matrixTaylorJetMap (↑u) N).comp (matrixTaylorJetMap (↑u⁻¹) N) = LinearMap.id := by
    rw [← matrixTaylorJetMap_mul,Units.mul_inv,matrixTaylorJetMap_one]
  have hli : Function.LeftInverse (matrixTaylorJetMap (↑u⁻¹) N) (matrixTaylorJetMap (↑u) N) := by
    intro v
    exact congrArg (fun f : (Fin N → ℂ × ℂ) →ₗ[ℂ] (Fin N → ℂ × ℂ) => f v) hl
  have hri : Function.RightInverse (matrixTaylorJetMap (↑u⁻¹) N) (matrixTaylorJetMap (↑u) N) := by
    intro v
    exact congrArg (fun f : (Fin N → ℂ × ℂ) →ₗ[ℂ] (Fin N → ℂ × ℂ) => f v) hr
  exact ⟨hli.injective,hri.surjective⟩

end NLS.ComplexAnalysis
