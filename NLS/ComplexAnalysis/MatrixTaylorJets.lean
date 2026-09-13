import NLS.ComplexAnalysis.ScalarTaylorJetNullity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Two-coordinate formal Taylor systems

A two-by-two formal matrix acts on finite pair-valued Taylor jets by scalar
convolution in each entry. Diagonal systems split into the two scalar kernels;
their eventual nullity is the order of their actual formal determinant.
-/

noncomputable section
open Complex PowerSeries Matrix
namespace NLS.ComplexAnalysis

/-- Truncated two-by-two formal multiplication, using pair coordinates at each Taylor level. -/
def matrixTaylorJetMap (A : Matrix (Fin 2) (Fin 2) (PowerSeries ℂ)) (N : ℕ) :
    (Fin N → ℂ × ℂ) →ₗ[ℂ] (Fin N → ℂ × ℂ) where
  toFun v k :=
    (scalarTaylorJetMap (A 0 0) N (fun j => (v j).1) k + scalarTaylorJetMap (A 0 1) N (fun j => (v j).2) k,
     scalarTaylorJetMap (A 1 0) N (fun j => (v j).1) k + scalarTaylorJetMap (A 1 1) N (fun j => (v j).2) k)
  map_add' := by
    intro u v
    have hfst (f : PowerSeries ℂ) : scalarTaylorJetMap f N (fun j => ((u+v) j).1) =
        scalarTaylorJetMap f N (fun j => (u j).1)+scalarTaylorJetMap f N (fun j => (v j).1) :=
      (scalarTaylorJetMap f N).map_add _ _
    have hsnd (f : PowerSeries ℂ) : scalarTaylorJetMap f N (fun j => ((u+v) j).2) =
        scalarTaylorJetMap f N (fun j => (u j).2)+scalarTaylorJetMap f N (fun j => (v j).2) :=
      (scalarTaylorJetMap f N).map_add _ _
    funext k
    rw [hfst,hsnd,hfst,hsnd]
    apply Prod.ext <;> dsimp <;> abel
  map_smul' := by
    intro c v
    have hfst (f : PowerSeries ℂ) : scalarTaylorJetMap f N (fun j => ((c • v) j).1) =
        c • scalarTaylorJetMap f N (fun j => (v j).1) := (scalarTaylorJetMap f N).map_smul c _
    have hsnd (f : PowerSeries ℂ) : scalarTaylorJetMap f N (fun j => ((c • v) j).2) =
        c • scalarTaylorJetMap f N (fun j => (v j).2) := (scalarTaylorJetMap f N).map_smul c _
    funext k
    rw [hfst,hsnd,hfst,hsnd]
    apply Prod.ext <;> dsimp <;> ring

/-- A diagonal formal matrix acts independently on the two scalar coefficient vectors. -/
theorem matrixTaylorJetMap_diagonal_apply (f g : PowerSeries ℂ) (N : ℕ) (v : Fin N → ℂ × ℂ) (k : Fin N) :
    matrixTaylorJetMap !![f,0;0,g] N v k =
      (scalarTaylorJetMap f N (fun j => (v j).1) k,scalarTaylorJetMap g N (fun j => (v j).2) k) := by
  simp [matrixTaylorJetMap,scalarTaylorJetMap_zero]

/-- A diagonal Taylor system vanishes exactly when both scalar Taylor systems vanish. -/
theorem mem_ker_matrixTaylorJetMap_diagonal (f g : PowerSeries ℂ) (N : ℕ) (v : Fin N → ℂ × ℂ) :
    v ∈ LinearMap.ker (matrixTaylorJetMap !![f,0;0,g] N) ↔
      (fun j => (v j).1) ∈ LinearMap.ker (scalarTaylorJetMap f N) ∧
      (fun j => (v j).2) ∈ LinearMap.ker (scalarTaylorJetMap g N) := by
  simp only [LinearMap.mem_ker,funext_iff,matrixTaylorJetMap_diagonal_apply,Pi.zero_apply,Prod.mk_eq_zero]
  exact forall_and

/-- The diagonal Taylor kernel is linearly the product of its two scalar kernels. -/
def diagonalTaylorKernelEquiv (f g : PowerSeries ℂ) (N : ℕ) :
    LinearMap.ker (matrixTaylorJetMap !![f,0;0,g] N) ≃ₗ[ℂ]
      (LinearMap.ker (scalarTaylorJetMap f N) × LinearMap.ker (scalarTaylorJetMap g N)) where
  toFun v := (⟨fun j => (v.val j).1,((mem_ker_matrixTaylorJetMap_diagonal f g N v).mp v.property).1⟩,
    ⟨fun j => (v.val j).2,((mem_ker_matrixTaylorJetMap_diagonal f g N v).mp v.property).2⟩)
  invFun v := ⟨fun j => (v.1.val j,v.2.val j),
    (mem_ker_matrixTaylorJetMap_diagonal f g N _).mpr ⟨v.1.property,v.2.property⟩⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- A diagonal Taylor system has the sum of the two truncated scalar orders as its exact nullity. -/
theorem finrank_ker_matrixTaylorJetMap_diagonal (f g : PowerSeries ℂ) (a b : ℕ)
    (hf : f.order = a) (hg : g.order = b) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap !![f,0;0,g] N)) = min N a+min N b := by
  rw [(diagonalTaylorKernelEquiv f g N).finrank_eq,Module.finrank_prod,
    finrank_ker_scalarTaylorJetMap f a hf,finrank_ker_scalarTaylorJetMap g b hg]

/-- Beyond both scalar orders, the diagonal nullity is their sum. -/
theorem finrank_ker_matrixTaylorJetMap_diagonal_of_order_le (f g : PowerSeries ℂ) (a b : ℕ)
    (hf : f.order = a) (hg : g.order = b) (N : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap !![f,0;0,g] N)) = a+b := by
  rw [finrank_ker_matrixTaylorJetMap_diagonal f g a b hf hg,min_eq_right ha,min_eq_right hb]

/-- For every diagonal formal matrix with nonzero diagonal entries, the eventual Taylor nullity is its determinant order. -/
theorem eventually_finrank_diagonalTaylorKernel_eq_det_order (f g : PowerSeries ℂ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Module.finrank ℂ (LinearMap.ker (matrixTaylorJetMap !![f,0;0,g] N)) : ℕ∞) =
        (Matrix.det !![f,0;0,g]).order := by
  refine Filter.eventually_atTop.mpr ⟨max f.order.toNat g.order.toNat,fun N hN => ?_⟩
  rw [finrank_ker_matrixTaylorJetMap_diagonal_of_order_le f g f.order.toNat g.order.toNat
    (PowerSeries.coe_toNat_order hf).symm (PowerSeries.coe_toNat_order hg).symm N
    ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)]
  simp only [Matrix.det_fin_two_of,mul_zero,sub_zero,PowerSeries.order_mul,ENat.natCast_add,
    PowerSeries.coe_toNat_order hf,PowerSeries.coe_toNat_order hg]

end NLS.ComplexAnalysis
