import NLS.ZakharovShabat.GapRootFactorGeometry
import NLS.ZakharovShabat.SourceCriticalRootRatioSourceAnalytic
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Exterior critical-root factors in Lemma 28.1

The hypotheses spell out the localization and critical-offset estimates
needed on the complex source neighborhood. The root and critical point
are the original canonical spectral objects. The finite-product bound
is uniform in the number of exterior factors.
-/
noncomputable section
open scoped ENNReal BigOperators
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Localization and the critical-offset estimate bound the actual single factor.
The coefficient one is stronger than the printed coefficient four thirds. -/
theorem source_exterior_critical_factor_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m n : ℤ) (z : ℂ) (hmn : m ≠ n)
    (hl : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
      (Real.pi:ℂ)*m‖ ≤ Real.pi/5)
    (hr : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
      (Real.pi:ℂ)*m‖ ≤ Real.pi/5)
    (hz : ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/5)
    (hc : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖ ≤
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖) :
    ‖(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z)/
      sourceStandardRoot hp hp1 ψ m z‖ ≤
      1+‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖/
        |((m-n:ℤ):ℝ)| := by
  have hmid := gap_midpoint_norm_sub_le _ _ _ _ hl hr
  have hsep := localized_endpoint_separation _ z m n hmn hmid hz
  have hd : (0:ℝ) < |((m-n:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hne : z ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro he
    rw [he] at hsep
    change (3/2:ℝ)*|((m-n:ℤ):ℝ)| ≤ ‖(canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m)-_‖ at hsep
    rw [sub_self,norm_zero] at hsep
    linarith
  exact localized_critical_root_factor_le _ _ z _ _ m n hmn hl hr hz
    (sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ m z hne) hc

/-- A norm majorant suffices for the finite product estimate; no estimate
on the complex difference of each factor from one is assumed. -/
theorem norm_finite_product_le_exp_of_norm_le {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (b : ι → ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1+b i) :
    ‖∏ i ∈ s, f i‖ ≤ Real.exp (∑ i ∈ s, b i) := by
  rw [norm_prod,Real.exp_sum]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi =>
    (hf i hi).trans (by linarith [Real.add_one_le_exp (b i)]))

/-- Cauchy--Schwarz turns a gap-square budget and a reciprocal-distance
budget into a finite-product bound. -/
theorem norm_finite_product_le_exp_sqrt_budgets {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (g d : ι → ℝ) (G R : ℝ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1+g i*d i)
    (hG : ∑ i ∈ s, (g i)^2 ≤ G) (hR : ∑ i ∈ s, (d i)^2 ≤ R) :
    ‖∏ i ∈ s, f i‖ ≤ Real.exp (Real.sqrt G*Real.sqrt R) := by
  have hG0 : 0 ≤ G := (Finset.sum_nonneg (fun i _ => sq_nonneg (g i))).trans hG
  have hR0 : 0 ≤ R := (Finset.sum_nonneg (fun i _ => sq_nonneg (d i))).trans hR
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s g d
  have hbudget := mul_le_mul hG hR (Finset.sum_nonneg (fun i _ => sq_nonneg (d i))) hG0
  have hsum : (∑ i ∈ s, g i*d i) ≤ Real.sqrt G*Real.sqrt R := by
    nlinarith [Real.sq_sqrt hG0,Real.sq_sqrt hR0,
      mul_nonneg (Real.sqrt_nonneg G) (Real.sqrt_nonneg R),
      sq_nonneg ((∑ i ∈ s, g i*d i)-Real.sqrt G*Real.sqrt R),
      show (Real.sqrt G*Real.sqrt R)^2=G*R by rw [mul_pow,Real.sq_sqrt hG0,Real.sq_sqrt hR0]]
  exact (norm_finite_product_le_exp_of_norm_le s f (fun i => g i*d i)
    hf).trans (Real.exp_le_exp.mpr hsum)

end NLS.ZakharovShabat
