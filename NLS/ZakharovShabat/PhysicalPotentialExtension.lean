import NLS.ZakharovShabat.PhysicalIntervalL2
import NLS.ZakharovShabat.ClassicalIntervalTransfer
import NLS.Fourier.FoldedEnergy

/-!
# Bounded analytic extension of original physical potentials

The Dirichlet-reflected Fourier potential is a continuous complex-linear map
from the original component-sum interval `L²` space into the actual Dirichlet
coefficient space. Its norm factor is exactly `1 / √2`, because the coefficients
use normalized measure on a doubled interval and the output pair uses a maximum
norm. The map is injective and agrees with the actual coefficients of every
original representative, including nonsmooth potentials.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- Addition is respected by physical coefficient synthesis almost everywhere. -/
theorem physicalBase_add (φ ψ : PairSpace 2) :
    physicalBase (φ + ψ) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => physicalBase φ x + physicalBase ψ x) := by
  have h₁ := circle_ae_pullback (Lp.coeFn_add (l2Synthesis φ.1) (l2Synthesis ψ.1))
  have h₂ := circle_ae_pullback (Lp.coeFn_add (l2Synthesis φ.2) (l2Synthesis ψ.2))
  filter_upwards [h₁, h₂] with x hx hy
  change (circlePullback (l2Synthesis (φ.1 + ψ.1)) x, circlePullback (l2Synthesis (φ.2 + ψ.2)) x) = _
  rw [map_add, map_add]
  exact Prod.ext hx hy

namespace BoundaryCondition

/-- The reflected potential coefficients only depend on the original `L²` class. -/
theorem dirichletPotentialCoefficients_congr_ae (φ ψ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1)))
    (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) :
    dirichletPotentialCoefficients φ hφ = dirichletPotentialCoefficients ψ hψ := by
  apply physicalBase_injective
  exact (physicalBase_dirichletPotentialCoefficients φ hφ).trans
    ((intervalExtension_congr_ae .dirichlet h).trans (physicalBase_dirichletPotentialCoefficients ψ hψ).symm)

/-- Extension of physical potentials is additive before bundling the `L²` space. -/
theorem dirichletPotentialCoefficients_add (φ ψ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1))) :
    dirichletPotentialCoefficients (φ + ψ) (hφ.add hψ) =
      dirichletPotentialCoefficients φ hφ + dirichletPotentialCoefficients ψ hψ := by
  apply physicalBase_injective
  filter_upwards [physicalBase_dirichletPotentialCoefficients (φ + ψ) (hφ.add hψ),
    physicalBase_dirichletPotentialCoefficients φ hφ, physicalBase_dirichletPotentialCoefficients ψ hψ,
    physicalBase_add (dirichletPotentialCoefficients φ hφ) (dirichletPotentialCoefficients ψ hψ)] with x hs h₁ h₂ ha
  rw [hs, ha, h₁, h₂]
  exact congrFun (map_add (intervalExtension .dirichlet) φ ψ) x

/-- The reflected potential coefficients respect complex scalar multiplication. -/
theorem dirichletPotentialCoefficients_smul (c : ℂ) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    dirichletPotentialCoefficients (c • φ) (hφ.const_smul c) = c • dirichletPotentialCoefficients φ hφ := by
  apply physicalBase_injective
  filter_upwards [physicalBase_dirichletPotentialCoefficients (c • φ) (hφ.const_smul c),
    physicalBase_dirichletPotentialCoefficients φ hφ,
    physicalBase_smul c (dirichletPotentialCoefficients φ hφ)] with x hs h₁ ha
  rw [hs, ha, h₁]
  exact congrFun (map_smul (intervalExtension .dirichlet) c φ) x

/-- Exact Parseval comparison with the ordinary component-sum energy of an original potential. -/
theorem norm_sq_dirichletPotentialCoefficients (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    ‖dirichletPotentialCoefficients φ hφ‖ ^ 2 = (1 / 2 : ℝ) *
      ((∫ x in (0 : ℝ)..1, ‖(φ x).1‖ ^ 2) + ∫ x in (0 : ℝ)..1, ‖(φ x).2‖ ^ 2) := by
  have h₁ := norm_sq_periodTwoL2Coefficients _ (memLp_intervalExtension .dirichlet φ hφ).fst
  have h₂ := norm_sq_periodTwoL2Coefficients _ (memLp_intervalExtension .dirichlet φ hφ).snd
  change ‖(dirichletPotentialCoefficients φ hφ).1‖ ^ 2 = (1 / 2 : ℝ) *
    ∫ x in (0 : ℝ)..2, ‖folded 1 (fun t => (φ t).1) (fun t => (φ t).2) x‖ ^ 2 at h₁
  change ‖(dirichletPotentialCoefficients φ hφ).2‖ ^ 2 = (1 / 2 : ℝ) *
    ∫ x in (0 : ℝ)..2, ‖folded 1 (fun t => (φ t).2) (fun t => (φ t).1) x‖ ^ 2 at h₂
  rw [integral_sq_folded_of_memLp 1 (by simp) hφ.fst hφ.snd] at h₁
  rw [integral_sq_folded_of_memLp 1 (by simp) hφ.snd hφ.fst] at h₂
  have he : ‖(dirichletPotentialCoefficients φ hφ).1‖ = ‖(dirichletPotentialCoefficients φ hφ).2‖ := by
    nlinarith [norm_nonneg (dirichletPotentialCoefficients φ hφ).1,
      norm_nonneg (dirichletPotentialCoefficients φ hφ).2]
  rw [Prod.norm_def, he, max_self]
  linarith

end BoundaryCondition
open BoundaryCondition

/-- Dirichlet extension of the representative of an original physical potential class. -/
def intervalPotentialCoefficients (u : IntervalPairL2) : PairSpace 2 :=
  dirichletPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u)

/-- The physical potential coefficients lie in the Dirichlet subspace used by both boundary operators. -/
theorem intervalPotentialCoefficients_mem (u : IntervalPairL2) :
    intervalPotentialCoefficients u ∈ dirichletSubspace :=
  dirichletPotentialCoefficients_mem _ (memLp_intervalL2Representative u)

@[simp] theorem intervalPotentialCoefficients_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    intervalPotentialCoefficients (intervalL2OfFunction φ hφ) = dirichletPotentialCoefficients φ hφ :=
  dirichletPotentialCoefficients_congr_ae _ _ _ _ (intervalL2Representative_ofFunction φ hφ)

/-- The exact squared-norm comparison, including normalization and the output pair norm. -/
theorem norm_sq_intervalPotentialCoefficients (u : IntervalPairL2) :
    ‖intervalPotentialCoefficients u‖ ^ 2 = (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
  rw [intervalPotentialCoefficients, norm_sq_dirichletPotentialCoefficients, norm_sq_intervalL2Representative]

/-- The physical norm is exactly `√2` times the norm of the reflected coefficient pair. -/
theorem norm_intervalPotentialCoefficients (u : IntervalPairL2) :
    ‖intervalPotentialCoefficients u‖ = (Real.sqrt 2 / 2) * ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg u))).mp
  rw [mul_pow, div_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), norm_sq_intervalPotentialCoefficients]
  ring

/-- The Fourier extension as a complex-linear map on original physical `L²` classes. -/
def intervalPotentialLinear : IntervalPairL2 →ₗ[ℂ] PairSpace 2 where
  toFun := intervalPotentialCoefficients
  map_add' u v := (dirichletPotentialCoefficients_congr_ae _ _ _ _ (intervalL2Representative_add u v)).trans
    (dirichletPotentialCoefficients_add _ _ (memLp_intervalL2Representative u) (memLp_intervalL2Representative v))
  map_smul' c u := (dirichletPotentialCoefficients_congr_ae _ _ _ _ (intervalL2Representative_smul c u)).trans
    (dirichletPotentialCoefficients_smul c _ (memLp_intervalL2Representative u))

/-- Bounded potential extension with its exact normalization constant. -/
def intervalPotentialCLM : IntervalPairL2 →L[ℂ] PairSpace 2 :=
  intervalPotentialLinear.mkContinuous (Real.sqrt 2 / 2) (fun u => (norm_intervalPotentialCoefficients u).le)

@[simp] theorem intervalPotentialCLM_apply (u : IntervalPairL2) :
    intervalPotentialCLM u = intervalPotentialCoefficients u := rfl

/-- Both original spectral problems use this same Dirichlet potential parameter map. -/
def intervalPotentialToDirichlet : IntervalPairL2 →L[ℂ] dirichletSubspace (p := 2) :=
  intervalPotentialCLM.codRestrict dirichletSubspace (fun u => dirichletPotentialCoefficients_mem _ (memLp_intervalL2Representative u))

@[simp] theorem intervalPotentialToDirichlet_coe (u : IntervalPairL2) :
    (intervalPotentialToDirichlet u : PairSpace 2) = intervalPotentialCoefficients u := rfl

theorem norm_intervalPotentialToDirichlet (u : IntervalPairL2) :
    ‖intervalPotentialToDirichlet u‖ = (Real.sqrt 2 / 2) * ‖u‖ := norm_intervalPotentialCoefficients u

theorem norm_intervalPotentialToDirichlet_le : ‖intervalPotentialToDirichlet‖ ≤ Real.sqrt 2 / 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => (norm_intervalPotentialToDirichlet u).le)

/-- Original physical potential dependence is complex analytic. -/
theorem analyticAt_intervalPotentialToDirichlet (u : IntervalPairL2) :
    AnalyticAt ℂ intervalPotentialToDirichlet u := intervalPotentialToDirichlet.analyticAt u

/-- Distinct original `L²` classes cannot give the same reflected coefficient potential. -/
theorem intervalPotentialToDirichlet_injective : Function.Injective intervalPotentialToDirichlet := by
  intro u v huv
  have hz : intervalPotentialToDirichlet (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have he := norm_intervalPotentialToDirichlet (u - v)
  rw [hz, norm_zero] at he
  have hs : 0 < Real.sqrt 2 / 2 := by positivity
  exact sub_eq_zero.mp (norm_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left (ne_of_gt hs)))

end NLS.ZakharovShabat
