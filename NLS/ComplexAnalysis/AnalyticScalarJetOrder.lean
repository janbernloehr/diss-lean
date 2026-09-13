import NLS.ComplexAnalysis.ScalarTaylorJetNullity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Analytic vanishing orders from scalar Taylor kernels

The ordinary coefficients of a convergent multilinear Taylor series form a
formal scalar series with exactly the analytic vanishing order. Thus finite
Taylor multiplication kernels detect that order, including the zero germ.
-/

noncomputable section
open Complex PowerSeries
namespace NLS.ComplexAnalysis

/-- Ordinary scalar coefficients of a one-variable multilinear Taylor series. -/
def scalarFormalTaylor (p : FormalMultilinearSeries ℂ ℂ ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => p n (fun _ => 1))

@[simp] theorem coeff_scalarFormalTaylor (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    PowerSeries.coeff n (scalarFormalTaylor p) = p n (fun _ => 1) := PowerSeries.coeff_mk n _

/-- Ordinary Taylor coefficients vanish exactly when the corresponding spectral derivatives vanish. -/
theorem scalarFormalTaylor_coeff_eq_zero_iff {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (n : ℕ) :
    PowerSeries.coeff n (scalarFormalTaylor p) = 0 ↔ iteratedDeriv n f z = 0 := by
  obtain ⟨r,hr⟩ := hf
  have h := hr.factorial_smul (1 : ℂ) n
  rw [iteratedDeriv_eq_iteratedFDeriv,← h,coeff_scalarFormalTaylor]
  simp [nsmul_eq_mul,Nat.factorial_ne_zero]

/-- Formal Taylor order and analytic vanishing order agree exactly, including infinite order. -/
theorem order_scalarFormalTaylor {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) : (scalarFormalTaylor p).order = analyticOrderAt f z := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.analyticAt]
  constructor
  · intro h j hj
    apply (scalarFormalTaylor_coeff_eq_zero_iff hf j).mp
    exact PowerSeries.coeff_of_lt_order j ((by exact_mod_cast hj : (j : ℕ∞) < n).trans_le h)
  · intro h
    exact PowerSeries.nat_le_order _ n (fun j hj => (scalarFormalTaylor_coeff_eq_zero_iff hf j).mpr (h j hj))

/-- A scalar analytic germ of finite order has Taylor nullity equal to the truncated vanishing order. -/
theorem finrank_scalarTaylorKernel_of_analyticOrder {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (m : ℕ) (hm : analyticOrderAt f z = m) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) = min N m :=
  finrank_ker_scalarTaylorJetMap _ m ((order_scalarFormalTaylor hf).trans hm) N

/-- The eventual scalar Taylor nullity is exactly the finite analytic vanishing order. -/
theorem eventually_finrank_scalarTaylorKernel_of_analyticOrder {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (m : ℕ) (hm : analyticOrderAt f z = m) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) = m := by
  refine Filter.eventually_atTop.mpr ⟨m,fun N hN => ?_⟩
  rw [finrank_scalarTaylorKernel_of_analyticOrder hf m hm,min_eq_right hN]

/-- Infinite analytic order gives the zero formal series and full nullity at every finite length. -/
theorem finrank_scalarTaylorKernel_of_analyticOrder_top {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {z : ℂ}
    (hf : HasFPowerSeriesAt f p z) (hm : analyticOrderAt f z = ⊤) (N : ℕ) :
    Module.finrank ℂ (LinearMap.ker (scalarTaylorJetMap (scalarFormalTaylor p) N)) = N := by
  have hz : scalarFormalTaylor p = 0 := PowerSeries.order_eq_top.mp ((order_scalarFormalTaylor hf).trans hm)
  rw [hz,finrank_ker_scalarTaylorJetMap_zero]

end NLS.ComplexAnalysis
