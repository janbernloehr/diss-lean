import NLS.ZakharovShabat.ClassicalAuxiliarySpectrum
import NLS.ZakharovShabat.PhysicalIntervalL2

/-!
# Auxiliary phase maps on the original physical L² space

The function and potential phases are isometries for the original component-sum
Lebesgue L² norm. Their representatives agree almost everywhere with the actual
pointwise physical transformations.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat

private theorem norm_phase_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : WithLp 2 (E × E)) : ‖WithLp.toLp 2 (u.ofLp.1, Complex.I • u.ofLp.2)‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg u)).mp
  simp [WithLp.prod_norm_sq_eq_of_L2, norm_smul]

private theorem norm_potential_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : WithLp 2 (E × E)) : ‖WithLp.toLp 2 (Complex.I • u.ofLp.1, -Complex.I • u.ofLp.2)‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg u)).mp
  simp [WithLp.prod_norm_sq_eq_of_L2, norm_smul]

private def pairPhase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    WithLp 2 (E × E) ≃ₗᵢ[ℂ] WithLp 2 (E × E) where
  toFun u := WithLp.toLp 2 (u.ofLp.1, Complex.I • u.ofLp.2)
  invFun u := WithLp.toLp 2 (u.ofLp.1, -Complex.I • u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [smul_add]
  map_smul' c u := by
    apply WithLp.ofLp_injective
    exact Prod.ext rfl (smul_comm Complex.I c u.ofLp.2)
  norm_map' u := norm_phase_pair u

private def pairPotential (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    WithLp 2 (E × E) ≃ₗᵢ[ℂ] WithLp 2 (E × E) where
  toFun u := WithLp.toLp 2 (Complex.I • u.ofLp.1, -Complex.I • u.ofLp.2)
  invFun u := WithLp.toLp 2 (-Complex.I • u.ofLp.1, Complex.I • u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [smul_add]
  map_smul' c u := by
    apply WithLp.ofLp_injective
    exact Prod.ext (smul_comm Complex.I c u.ofLp.1) (smul_comm (-Complex.I) c u.ofLp.2)
  norm_map' u := norm_potential_pair u

/-- The function phase on original physical L² classes. -/
def intervalAuxiliaryPhase : IntervalPairL2 ≃ₗᵢ[ℂ] IntervalPairL2 := pairPhase IntervalL2

/-- The potential phase on original physical L² classes. -/
def intervalAuxiliaryPotential : IntervalPairL2 ≃ₗᵢ[ℂ] IntervalPairL2 := pairPotential IntervalL2

theorem intervalL2Representative_auxiliaryPhase (u : IntervalPairL2) :
    intervalL2Representative (intervalAuxiliaryPhase u) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalAuxiliaryPhase (intervalL2Representative u) := by
  filter_upwards [Lp.coeFn_smul Complex.I u.ofLp.2] with x hx
  exact Prod.ext rfl hx

theorem intervalL2Representative_auxiliaryPhase_symm (u : IntervalPairL2) :
    intervalL2Representative (intervalAuxiliaryPhase.symm u) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalAuxiliaryPhase.symm (intervalL2Representative u) := by
  filter_upwards [Lp.coeFn_smul (-Complex.I) u.ofLp.2] with x hx
  exact Prod.ext rfl hx

theorem intervalL2Representative_auxiliaryPotential (u : IntervalPairL2) :
    intervalL2Representative (intervalAuxiliaryPotential u) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalAuxiliaryPotential (intervalL2Representative u) := by
  filter_upwards [Lp.coeFn_smul Complex.I u.ofLp.1, Lp.coeFn_smul (-Complex.I) u.ofLp.2] with x hx hy
  exact Prod.ext hx hy

/-- Applying the phase to any original representative gives the same physical L² class. -/
theorem intervalAuxiliaryPhase_ofFunction (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp (physicalAuxiliaryPhase f) 2 (volume.restrict (Ioc 0 1))) :
    intervalAuxiliaryPhase (intervalL2OfFunction f hf) = intervalL2OfFunction (physicalAuxiliaryPhase f) hg := by
  apply intervalL2Representative_injective
  apply (intervalL2Representative_auxiliaryPhase _).trans
  apply ((intervalL2Representative_ofFunction f hf).fun_comp (auxiliaryPhase ℂ)).trans
  exact (intervalL2Representative_ofFunction _ _).symm

end NLS.ZakharovShabat
