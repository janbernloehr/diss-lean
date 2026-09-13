import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Power series for globally complex smooth scalar-valued maps

The Fréchet Taylor coefficients have positive convergence radius by Schwarz
bounds. Their diagonal evaluations agree with the Taylor coefficients along
complex affine lines. The one-variable Cauchy theorem identifies the sum with
the original function, proving Banach-space analyticity.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal NNReal ContDiff
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Affine-line derivatives are diagonal evaluations of the full Fréchet derivatives. -/
theorem iteratedDeriv_affineLine_eq (f : E → ℂ) (hf : ContDiff ℂ ∞ f) (c y : E) (n : ℕ) :
    iteratedDeriv n (fun a : ℂ => f (c+a • y)) 0 =
      iteratedFDeriv ℂ n f c (fun _ : Fin n => y) := by
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight y
  have hk : ContDiff ℂ ∞ (fun z : E => f (c+z)) := hf.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℂ n ((fun z : E => f (c+z)) ∘ L) 0 (fun _ => 1) = _
  rw [L.iteratedFDeriv_comp_right hk 0 (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, iteratedFDeriv_comp_add_left]

/-- The factorial-normalized Taylor series of an entire scalar function sums to its value at one. -/
theorem hasSum_entire_taylor_one (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    HasSum (fun n : ℕ => iteratedDeriv n f 0/(n.factorial : ℂ)) (f 1) := by
  have hp := hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries (hf.analyticAt 0).hasFPowerSeriesAt
  rw [he] at hp
  have hs := hp.hasSum (y := 1) (by simp)
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, FormalMultilinearSeries.coeff_ofScalars, Finset.prod_const_one, smul_eq_mul,
    one_mul, zero_add] using hs

/-- The full Fréchet Taylor series sums correctly along every fixed direction. -/
theorem hasSum_complexTaylorSeries (f : E → ℂ) (hf : ContDiff ℂ ∞ f) (c y : E) :
    HasSum (fun n : ℕ => complexTaylorSeries f c n (fun _ : Fin n => y)) (f (c+y)) := by
  have hg : Differentiable ℂ (fun a : ℂ => f (c+a • y)) :=
    (hf.differentiable (by simp)).comp (by fun_prop)
  have hs := hasSum_entire_taylor_one _ hg
  simpa only [iteratedDeriv_affineLine_eq f hf c y, complexTaylorSeries,
    smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm,
    one_smul] using hs

/-- A globally complex smooth scalar-valued function has its Fréchet power series on a positive-radius ball. -/
theorem hasFPowerSeriesOnBall_of_complexSmooth (f : E → ℂ) (hf : ContDiff ℂ ∞ f) (c : E) :
    HasFPowerSeriesOnBall f (complexTaylorSeries f c) c (complexTaylorSeries f c).radius :=
  ⟨le_rfl,complexTaylorSeries_radius_pos f hf c,fun {_} _ => hasSum_complexTaylorSeries f hf c _⟩

/-- Global complex Fréchet smoothness gives Banach-space analyticity for scalar-valued functions. -/
theorem analyticOnNhd_of_complexSmooth (f : E → ℂ) (hf : ContDiff ℂ ∞ f) :
    AnalyticOnNhd ℂ f Set.univ :=
  fun c _ => (hasFPowerSeriesOnBall_of_complexSmooth f hf c).analyticAt

end NLS.ComplexAnalysis
