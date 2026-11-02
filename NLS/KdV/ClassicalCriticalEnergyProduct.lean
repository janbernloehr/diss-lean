import NLS.KdV.ClassicalSignedCriticalProduct
import NLS.ComplexAnalysis.SquareProductConvergence

/-! # The exact positive-index Hill discriminant derivative product

Pair the selected signed frequency roots into the actual positive energy
critical roots. The literal normalized energy cutoffs converge locally
uniformly everywhere, including zero and every collapsed critical energy.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillCriticalEnergyPartialProduct (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ)
    (lambda : ℂ) (M : ℕ) : ℂ :=
  -∏ j ∈ Finset.range M,
    (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q-lambda)/
      ((Real.pi : ℂ)*((j : ℂ)+1))^2

theorem classicalHillSignedPartialProduct_eq_energy (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ)
    (z : ℂ) (M : ℕ) :
    singleSpectralPartialProduct (classicalHillSignedCritical N q) z M =
      (2*z)*classicalHillCriticalEnergyPartialProduct N q (z^2) M := by
  rw [singleSpectralPartialProduct,prod_symmetric_interval]
  have hp (j : ℕ) :
      singleSpectralFactor (classicalHillSignedCritical N q) z ((j : ℤ)+1)*
        singleSpectralFactor (classicalHillSignedCritical N q) z (-((j : ℤ)+1)) =
      (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q-z^2)/
        ((Real.pi : ℂ)*((j : ℂ)+1))^2 := by
    have hpos : classicalHillSignedCritical N q ((j : ℤ)+1) =
        Complex.sqrt (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q) := by
      simpa only [Nat.cast_add,Nat.cast_one] using!
        classicalHillSignedCritical_positive N q (⟨j+1,by omega⟩ : ℕ+)
    have hneg : classicalHillSignedCritical N q (-((j : ℤ)+1)) =
        -Complex.sqrt (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q) := by
      simpa only [Nat.cast_add,Nat.cast_one] using!
        classicalHillSignedCritical_negative N q (⟨j+1,by omega⟩ : ℕ+)
    simp only [singleSpectralFactor,singleSpectralDenominator,
      if_neg (by omega : (j : ℤ)+1 ≠ 0),if_neg (by omega : -((j : ℤ)+1) ≠ 0),hpos,hneg,
      Int.cast_add,Int.cast_one,Int.cast_natCast,Int.cast_neg,mul_neg]
    let w := Complex.sqrt (classicalHillUniformCriticalPoint N (⟨j+1,by omega⟩ : ℕ+) q)
    let a : ℂ := (Real.pi : ℂ)*((j : ℂ)+1)
    have ha : a ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (Nat.cast_add_one_ne_zero j)
    have he : ((w-z)/a)*((-w-z)/(-a)) = (w^2-z^2)/a^2 := by field_simp; ring
    simpa only [w,a,sq_sqrt] using he
  simp only [hp]
  simp only [singleSpectralFactor,singleSpectralDenominator,classicalHillSignedCritical_zero,
    ite_true,zero_sub,div_one]
  dsimp only [classicalHillCriticalEnergyPartialProduct]
  ring

theorem analyticOnNhd_classicalHillCriticalEnergyPartialProduct
    (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (M : ℕ) :
    AnalyticOnNhd ℂ (fun z => classicalHillCriticalEnergyPartialProduct N q z M) univ := by
  intro z _
  apply AnalyticAt.neg
  exact Finset.analyticAt_fun_prod _ (fun j _ => (analyticAt_const.sub analyticAt_id).div_const)

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

/-- The exact source-sign derivative product over the actual selected
positive energy critical roots, on the same normalization neighborhood. -/
theorem critical_energy_product (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    TendstoLocallyUniformlyOn (fun M lambda => classicalHillCriticalEnergyPartialProduct N q lambda M)
      (deriv (classicalHillDiscriminant q)) atTop univ := by
  apply tendstoLocallyUniformlyOn_of_square_pullback
    (fun M lambda => classicalHillCriticalEnergyPartialProduct N q lambda M)
    (deriv (classicalHillDiscriminant q))
    (fun M => differentiableOn_univ.mp
      (analyticOnNhd_classicalHillCriticalEnergyPartialProduct N q M).differentiableOn)
    (analyticOnNhd_classicalHillDiscriminant q).deriv.continuous
  have he (M : ℕ) (z : ℂ) :
      (2*z)*classicalHillCriticalEnergyPartialProduct N q (z^2) M =
        singleSpectralPartialProduct (classicalHillSignedCritical N q) z M :=
    (classicalHillSignedPartialProduct_eq_energy N q z M).symm
  simpa only [he] using (D.signedCritical_product q hq).2.2.2

theorem critical_energy_product_at (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (lambda : ℂ) :
    Tendsto (classicalHillCriticalEnergyPartialProduct N q lambda) atTop
      (𝓝 (deriv (classicalHillDiscriminant q) lambda)) :=
  (D.critical_energy_product q hq).tendsto_at (mem_univ _)

end ClassicalAllContourPeriodData
end NLS.KdV
