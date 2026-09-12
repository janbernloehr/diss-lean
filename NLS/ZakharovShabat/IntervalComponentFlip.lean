import NLS.ZakharovShabat.PhysicalPotentialExtension

/-!
# Component sign changes for physical and coefficient boundary spaces

Negating the second component is a complex-linear isometric involution. Applied
before and after Dirichlet reflection it gives Neumann reflection. All physical
identities for `L²` representatives are a.e. identities.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The physical component sign change, without complex conjugation. -/
def componentFlip (v : ℂ × ℂ) : ℂ × ℂ := (v.1, -v.2)

/-- Negating the second original `L²` component preserves the physical Hilbert norm. -/
def intervalComponentFlip : IntervalPairL2 ≃ₗᵢ[ℂ] IntervalPairL2 where
  toFun u := WithLp.toLp 2 (u.ofLp.1, -u.ofLp.2)
  invFun u := WithLp.toLp 2 (u.ofLp.1, -u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [add_comm]
  map_smul' c u := by apply WithLp.ofLp_injective; simp [smul_neg]
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg u)).mp
    simp [WithLp.prod_norm_sq_eq_of_L2]

@[simp] theorem intervalComponentFlip_ofLp (u : IntervalPairL2) :
    (intervalComponentFlip u).ofLp = (u.ofLp.1, -u.ofLp.2) := rfl

@[simp] theorem intervalComponentFlip_involutive (u : IntervalPairL2) :
    intervalComponentFlip (intervalComponentFlip u) = u := intervalComponentFlip.left_inv u

/-- The isometry negates precisely the second physical component almost everywhere. -/
theorem intervalL2Representative_componentFlip (u : IntervalPairL2) :
    intervalL2Representative (intervalComponentFlip u) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => componentFlip (intervalL2Representative u x)) := by
  filter_upwards [Lp.coeFn_neg u.ofLp.2] with x hx
  exact Prod.ext rfl hx

/-- The same component sign change identifies the two coefficient boundary subspaces. -/
def dirichletToNeumann : dirichletSubspace (p := 2) ≃ₗᵢ[ℂ] neumannSubspace (p := 2) where
  toFun a := ⟨(a.val.1, -a.val.2), by
    rw [mem_neumannSubspace]
    intro n
    simpa using ((mem_dirichletSubspace a.val).mp a.property n)⟩
  invFun a := ⟨(a.val.1, -a.val.2), by
    rw [mem_dirichletSubspace]
    intro n
    exact (mem_neumannSubspace a.val).mp a.property n⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp
  map_add' a b := by apply Subtype.ext; simp [add_comm]
  map_smul' c a := by apply Subtype.ext; simp [smul_neg]
  norm_map' a := by change max ‖a.val.1‖ ‖-a.val.2‖ = max ‖a.val.1‖ ‖a.val.2‖; rw [norm_neg]

@[simp] theorem dirichletToNeumann_coe (a : dirichletSubspace (p := 2)) :
    (dirichletToNeumann a).val = (a.val.1, -a.val.2) := rfl

/-- Coefficient sign change realizes physical component sign change. -/
theorem physicalBase_componentFlip (a : PairSpace 2) :
    physicalBase (a.1, -a.2) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => componentFlip (physicalBase a x)) := by
  have h := circle_ae_pullback (Lp.coeFn_neg (l2Synthesis a.2))
  filter_upwards [h] with x hx
  change (circlePullback (l2Synthesis a.1) x, circlePullback (l2Synthesis (-a.2)) x) = _
  rw [map_neg]
  exact Prod.ext rfl hx

namespace BoundaryCondition

/-- Neumann extension is Dirichlet extension with a second-component sign change on each side. -/
theorem intervalExtension_neumann_componentFlip (f : ℝ → ℂ × ℂ) (x : ℝ) :
    componentFlip (intervalExtension .dirichlet (fun t => componentFlip (f t)) x) =
      intervalExtension .neumann f x := by
  by_cases hx : x ≤ 1 <;> simp [intervalExtension, folded, extensionSign, componentFlip, hx]

end BoundaryCondition
end NLS.ZakharovShabat
