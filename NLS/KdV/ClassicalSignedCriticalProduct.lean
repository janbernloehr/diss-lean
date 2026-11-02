import NLS.KdV.ClassicalNormalizedDifferentials
import NLS.ZakharovShabat.NearFreeCriticalRelabeling
import NLS.ZakharovShabat.DiscriminantDerivativeProduct

/-! # The exact derivative product for the selected actual Hill critical roots

Reflect the positive energy roots into signed frequency roots and retain
zero. The complete spectral labeling and normalized derivative product
are proved for precisely this selected family, without a real-type input.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillSignedCritical (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (n : ℤ) : ℂ :=
  if hn : 0 < n then Complex.sqrt (classicalHillUniformCriticalPoint N (positiveIntegerIndex n hn) q)
  else if hn : n < 0 then -Complex.sqrt (classicalHillUniformCriticalPoint N
    (positiveIntegerIndex (-n) (by omega)) q) else 0

theorem classicalHillSignedCritical_zero (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) :
    classicalHillSignedCritical N q 0 = 0 := by simp [classicalHillSignedCritical]

theorem classicalHillSignedCritical_positive (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) :
    classicalHillSignedCritical N q (n : ℤ) = Complex.sqrt (classicalHillUniformCriticalPoint N n q) := by
  rw [classicalHillSignedCritical,dif_pos (by exact_mod_cast n.pos)]
  congr 2

theorem classicalHillSignedCritical_negative (N : ℕ) (q : NLS.LinearVolterra.Curve ℂ) (n : ℕ+) :
    classicalHillSignedCritical N q (-(n : ℤ)) = -Complex.sqrt (classicalHillUniformCriticalPoint N n q) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  rw [classicalHillSignedCritical,dif_neg (by omega : ¬ 0 < -(n : ℤ)),
    dif_pos (by omega : -(n : ℤ) < 0)]
  congr 3
  apply Subtype.ext
  change (-(-(n : ℤ))).toNat = (n : ℕ)
  simp only [neg_neg,Int.toNat_natCast]

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem signedCritical_is_critical (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (n : ℤ) :
    deriv (canonicalDiscriminant (by simp) (classicalHillCoefficientPotential q))
      (classicalHillSignedCritical N q n) = 0 := by
  by_cases hn : 0 < n
  · rw [classicalHillSignedCritical,dif_pos hn,classicalHill_frequency_derivative_eq,sq_sqrt,
      D.critical_zero _ q hq,mul_zero]
  by_cases hn0 : n < 0
  · rw [classicalHillSignedCritical,dif_neg hn,dif_pos hn0,classicalHill_frequency_derivative_eq,
      neg_sq,sq_sqrt,D.critical_zero _ q hq,mul_zero]
  have he : n = 0 := by omega
  rw [he,classicalHillSignedCritical_zero,classicalHill_frequency_derivative_eq]
  ring

theorem signedCritical_close (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (n : ℤ) :
    ‖classicalHillSignedCritical N q n-(Real.pi : ℂ)*n‖ < Real.pi/8 := by
  by_cases hn : 0 < n
  · rw [classicalHillSignedCritical,dif_pos hn]
    have he : (positiveIntegerIndex n hn : ℂ) = (n : ℂ) := by exact_mod_cast positiveIntegerIndex_int n hn
    simpa only [he] using D.critical_close (positiveIntegerIndex n hn) q hq
  by_cases hn0 : n < 0
  · rw [classicalHillSignedCritical,dif_neg hn,dif_pos hn0]
    let k := positiveIntegerIndex (-n) (by omega : 0 < -n)
    have he : (k : ℂ) = -(n : ℂ) := by exact_mod_cast positiveIntegerIndex_int (-n) (by omega)
    have hc := D.critical_close k q hq
    rw [he] at hc
    have heq : -Complex.sqrt (classicalHillUniformCriticalPoint N k q)-(Real.pi : ℂ)*n =
        -(Complex.sqrt (classicalHillUniformCriticalPoint N k q)-(Real.pi : ℂ)*(-(n : ℂ))) := by ring
    change ‖-Complex.sqrt (classicalHillUniformCriticalPoint N k q)-(Real.pi : ℂ)*n‖ < _
    rw [heq,norm_neg]
    exact hc
  have he : n = 0 := by omega
  rw [he,classicalHillSignedCritical_zero,Int.cast_zero,mul_zero,sub_zero,norm_zero]
  positivity

/-- The complete signed product uses exactly the selected positive energy
critical roots, including the finite head, rather than an arbitrary labeling. -/
theorem signedCritical_product (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    (∃ M : ℕ, CriticalPointLabeling (by simp) (by norm_num) (classicalHillCoefficientPotential q)
      (classicalHillCoefficientPotential_even q) M (classicalHillSignedCritical N q)) ∧
    Memℓp (fun n => classicalHillSignedCritical N q n-(Real.pi : ℂ)*n) 2 ∧
    (∀ z : ℂ, entireSingleSpectralProduct (classicalHillSignedCritical N q) z =
      (2*z)*deriv (classicalHillDiscriminant q) (z^2)) ∧
    TendstoLocallyUniformlyOn
      (fun M z => singleSpectralPartialProduct (classicalHillSignedCritical N q) z M)
      (fun z => (2*z)*deriv (classicalHillDiscriminant q) (z^2)) atTop univ := by
  obtain ⟨M,η,hη,hηlp⟩ := exists_criticalPointLabeling_memℓp (by simp) (by norm_num)
    (classicalHillCoefficientPotential q) (classicalHillCoefficientPotential_even q)
  have hlabel := (hη.relabel_of_near_free (classicalHillSignedCritical N q)
    (D.signedCritical_is_critical q hq) (D.signedCritical_close q hq)).1
  have hlp := hη.memℓp_of_near_free_relabeling hηlp (classicalHillSignedCritical N q)
    (D.signedCritical_is_critical q hq) (D.signedCritical_close q hq)
  have he (z : ℂ) := (hlabel.product_eq_derivative hlp z).trans
    (classicalHill_frequency_derivative_eq q z)
  exact ⟨⟨M,hlabel⟩,hlp,he,
    (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by simp) _ hlp).congr_right
      (fun z _ => he z)⟩

end ClassicalAllContourPeriodData
end NLS.KdV
