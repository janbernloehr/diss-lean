import NLS.KdV.ClassicalCriticalEnergyProduct
import NLS.ComplexAnalysis.RemovableFactorConvergence

/-! # Exact omitted critical products for the entire numerator basis

The actual filled basis B_n is the canonical positive critical product
with its own factor removed and prefactor 2/(n*pi). This concerns the
critical basis; the normalized Psi_n have different, still-to-be-identified
canonical zeros at nonzero potentials.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillCriticalBasisPartialProduct (N : ℕ) (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ)
    (lambda : ℂ) (M : ℕ) : ℂ :=
  (2/((n : ℂ)*Real.pi))*∏ j ∈ (Finset.range M).erase ((n : ℕ)-1),
    (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q-lambda)/
      ((Real.pi : ℂ)*((j : ℂ)+1))^2

theorem classicalHillCriticalBasisPartialProduct_factor (N : ℕ) (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) (M : ℕ) (hM : (n : ℕ) ≤ M) :
    (lambda-classicalHillUniformCriticalPoint N n q)*classicalHillCriticalBasisPartialProduct N n q lambda M =
      (2*(n : ℂ)*Real.pi)*classicalHillCriticalEnergyPartialProduct N q lambda M := by
  let i := (n : ℕ)-1
  have hi : i+1 = (n : ℕ) := Nat.sub_add_cancel n.property
  have himem : i ∈ Finset.range M := Finset.mem_range.mpr (by dsimp only [i]; omega)
  have hnidx : (⟨i+1,by omega⟩ : ℕ+) = n := Subtype.ext hi
  have hcast : (i : ℂ)+1 = (n : ℂ) := by exact_mod_cast hi
  let f : ℕ → ℂ := fun j =>
    (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q-lambda)/
      ((Real.pi : ℂ)*((j : ℂ)+1))^2
  have hfi : f i = (classicalHillUniformCriticalPoint N n q-lambda)/((n : ℂ)*Real.pi)^2 := by
    dsimp only [f]
    rw [hnidx,hcast,mul_comm (Real.pi : ℂ)]
  have hprod := Finset.mul_prod_erase (Finset.range M) f himem
  change (lambda-classicalHillUniformCriticalPoint N n q)*
    ((2/((n : ℂ)*Real.pi))*∏ j ∈ (Finset.range M).erase i, f j) =
      (2*(n : ℂ)*Real.pi)*(-(∏ j ∈ Finset.range M, f j))
  rw [← hprod,hfi]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

theorem analyticOnNhd_classicalHillCriticalBasisPartialProduct
    (N : ℕ) (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (M : ℕ) :
    AnalyticOnNhd ℂ (fun z => classicalHillCriticalBasisPartialProduct N n q z M) univ := by
  intro z _
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _
    (fun j _ => (analyticAt_const.sub analyticAt_id).div_const))

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

/-- The filled own critical energy is included in the locally uniform
canonical product limit, with the exact source-scale prefactor. -/
theorem critical_basis_product (n : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    TendstoLocallyUniformlyOn (fun M lambda => classicalHillCriticalBasisPartialProduct N n q lambda M)
      (fun lambda => classicalHillUniformNumerator N n (lambda,q)) atTop univ := by
  have hB : AnalyticOnNhd ℂ (fun lambda => classicalHillUniformNumerator N n (lambda,q)) univ := by
    intro z _
    exact (D.numerator_analytic n (z,q) ⟨mem_univ _,hq⟩).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  apply tendstoLocallyUniformlyOn_of_linear_factor _ _
    (fun M => differentiableOn_univ.mp
      (analyticOnNhd_classicalHillCriticalBasisPartialProduct N n q M).differentiableOn)
    hB.continuous (classicalHillUniformCriticalPoint N n q)
  let L : ℂ →L[ℂ] ℂ := (2*(n : ℂ)*Real.pi) • ContinuousLinearMap.id ℂ ℂ
  have hc := L.uniformContinuous.comp_tendstoLocallyUniformlyOn (D.critical_energy_product q hq)
  have hc' : TendstoLocallyUniformlyOn
      (fun M z => (2*(n : ℂ)*Real.pi)*classicalHillCriticalEnergyPartialProduct N q z M)
      (fun z => (2*(n : ℂ)*Real.pi)*deriv (classicalHillDiscriminant q) z) atTop univ := by
    simpa only [L,Function.comp_def,smul_apply,smul_eq_mul,ContinuousLinearMap.id_apply] using! hc
  have he : ∀ᶠ M : ℕ in atTop, ∀ z ∈ (univ : Set ℂ),
      Inseparable ((2*(n : ℂ)*Real.pi)*classicalHillCriticalEnergyPartialProduct N q z M)
        ((z-classicalHillUniformCriticalPoint N n q)*classicalHillCriticalBasisPartialProduct N n q z M) := by
    filter_upwards [eventually_ge_atTop (n : ℕ)] with M hM z _
    exact Inseparable.of_eq (classicalHillCriticalBasisPartialProduct_factor N n q z M hM).symm
  exact (hc'.congr_inseparable he).congr_right (fun z _ => (D.numerator_factor n q hq z).symm)

end ClassicalAllContourPeriodData

/-- One constructed neighborhood supports the actual derivative product and
every filled critical basis product, before all potential and mode indices. -/
theorem exists_classicalHill_critical_products :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      0 < N ∧ IsOpen V ∧ (0 : NLS.LinearVolterra.Curve ℂ) ∈ V ∧
      ∀ q ∈ V,
        TendstoLocallyUniformlyOn
          (fun M lambda => classicalHillCriticalEnergyPartialProduct N q lambda M)
          (deriv (classicalHillDiscriminant q)) atTop univ ∧
        ∀ n : ℕ+, TendstoLocallyUniformlyOn
          (fun M lambda => classicalHillCriticalBasisPartialProduct N n q lambda M)
          (fun lambda => classicalHillUniformNumerator N n (lambda,q)) atTop univ := by
  obtain ⟨N,V,A,hN,D⟩ := exists_classicalHill_all_contour_period_data
  exact ⟨N,V,hN,D.isOpen,D.zero_mem,fun q hq =>
    ⟨D.critical_energy_product q hq,fun n => D.critical_basis_product n q hq⟩⟩

end NLS.KdV
