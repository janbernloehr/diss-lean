import NLS.SequenceSpaces.QuadraticFrequencyAnalytic
import NLS.SequenceSpaces.Reflection

/-! The positive frequency displacement extends ODDLY to signed l2
coefficients. This is an analytic coordinate transformation of independent
energy data, not an assertion that its roots are Dirac eigenvalues. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

def positiveOddInsert (a : lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  positiveInsert a-Coeff.reflection (positiveInsert a)

theorem positiveOddInsert_positive (a : lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    positiveOddInsert a ((m:ℕ):ℤ) = a m := by
  change positiveInsert a ((m:ℕ):ℤ)-positiveInsert a (-((m:ℕ):ℤ)) = a m
  rw [positiveInsert_apply,positiveInsert_apply_nonpos a _ (by have hp := m.pos; omega),sub_zero]

theorem positiveOddInsert_zero (a : lp (fun _ : ℕ+ => ℂ) 2) : positiveOddInsert a 0 = 0 := by
  change positiveInsert a 0-positiveInsert a (-0) = 0
  simp only [neg_zero,sub_self]

theorem positiveOddInsert_neg (a : lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) :
    positiveOddInsert a (-k) = -positiveOddInsert a k := by
  change positiveInsert a (-k)-positiveInsert a (-(-k)) = -(positiveInsert a k-positiveInsert a (-k))
  rw [neg_neg]
  ring

def positiveOddInsertCLM : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] Coeff 2 :=
  positiveInsertIsometry.toContinuousLinearMap-
    Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp positiveInsertIsometry.toContinuousLinearMap

theorem positiveOddInsertCLM_apply (a : lp (fun _ : ℕ+ => ℂ) 2) : positiveOddInsertCLM a = positiveOddInsert a := rfl

theorem norm_positiveOddInsert_le (a : lp (fun _ : ℕ+ => ℂ) 2) : ‖positiveOddInsert a‖ ≤ 2*‖a‖ := by
  have h := norm_sub_le (positiveInsert a) (Coeff.reflection (positiveInsert a))
  rw [Coeff.reflection.norm_map,norm_positiveInsert] at h
  simpa only [positiveOddInsert,two_mul] using h

def balancedFrequencyDisplacement (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : Coeff 2 :=
  positiveOddInsert (positiveFrequencyDisplacement α hα t)

def balancedFrequency (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) : ℂ :=
  (α:ℂ)*k+balancedFrequencyDisplacement α hα t k

theorem balancedFrequency_zero (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : balancedFrequency α hα t 0 = 0 := by
  simp only [balancedFrequency,Int.cast_zero,mul_zero,balancedFrequencyDisplacement,positiveOddInsert_zero,add_zero]

theorem balancedFrequency_neg (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (k : ℤ) :
    balancedFrequency α hα t (-k) = -balancedFrequency α hα t k := by
  simp only [balancedFrequency,Int.cast_neg,mul_neg,balancedFrequencyDisplacement,positiveOddInsert_neg]
  ring

theorem balancedFrequency_positive (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    balancedFrequency α hα t ((m:ℕ):ℤ) = Complex.sqrt (quadraticLatticeEnergy α m t) := by
  simp only [balancedFrequency,Int.cast_natCast,balancedFrequencyDisplacement,
    positiveOddInsert_positive,positiveFrequencyDisplacement_apply,add_sub_cancel]

theorem balancedFrequency_positive_sq (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    balancedFrequency α hα t ((m:ℕ):ℤ)^2 = quadraticLatticeEnergy α m t := by
  rw [balancedFrequency_positive,NLS.ComplexAnalysis.complex_sqrt_sq]

theorem norm_balancedFrequencyDisplacement_le (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    ‖balancedFrequencyDisplacement α hα t‖ ≤ 2*α⁻¹*(‖t.2‖+2*‖t.1‖) :=
  (norm_positiveOddInsert_le _).trans ((mul_le_mul_of_nonneg_left
    (norm_positiveFrequencyDisplacement_le α hα t) (by norm_num)).trans_eq (by ring))

theorem memlp_balancedFrequency_displacement (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    Memℓp (fun k => balancedFrequency α hα t k-(α:ℂ)*k) 2 := by
  simpa only [balancedFrequency,add_sub_cancel_left] using lp.memℓp (balancedFrequencyDisplacement α hα t)

theorem analyticOnNhd_balancedFrequencyDisplacement (α : ℝ) (hα : 0 < α) :
    AnalyticOnNhd ℂ (balancedFrequencyDisplacement α hα) (quadraticFrequencyDomain α) := by
  intro t ht
  have h := (positiveOddInsertCLM.analyticAt _).comp
    (analyticOnNhd_positiveFrequencyDisplacement α hα t ht)
  simpa only [Function.comp_def,positiveOddInsertCLM_apply,balancedFrequencyDisplacement] using! h

end NLS.LpSequence
