import NLS.SequenceSpaces.PositiveCartesianParameters
import NLS.SequenceSpaces.RealCoeffNorm

/-! # Real normalized parameters for positive Cartesian pairs and signed mean -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

def positiveCartesianRealParameters : PositiveCartesianTarget w p →L[ℝ] (RealCoeff p × RealCoeff p) :=
  ((Coeff.reCLM p).prodMap (Coeff.reCLM p)).comp
    ((positiveCartesianParameterSection w p).restrictScalars ℝ)

@[simp] theorem positiveCartesianRealParameters_fst (z : PositiveCartesianTarget w p) (n : ℤ) :
    (positiveCartesianRealParameters w p z).1 n =
      w n*(z.1.1.val.val n).re+if n = 0 then z.2.re else 0 := by
  change ((positiveCartesianParameterSection w p z).1 n).re = _
  rw [positiveCartesianParameterSection_fst]
  split_ifs <;> simp

@[simp] theorem positiveCartesianRealParameters_snd (z : PositiveCartesianTarget w p) (n : ℤ) :
    (positiveCartesianRealParameters w p z).2 n = w n*(z.1.2.val.val n).re := by
  change ((positiveCartesianParameterSection w p z).2 n).re = _
  rw [positiveCartesianParameterSection_snd]
  simp

theorem complex_positiveCartesianRealParameters (z : PositiveCartesianTarget w p)
    (hr : ∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0) (hm : z.2.im = 0) :
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) (positiveCartesianRealParameters w p z) =
      positiveCartesianParameterSection w p z := by
  change (RealCoeff.complexCLM p (Coeff.reCLM p (positiveCartesianParameterSection w p z).1),
    RealCoeff.complexCLM p (Coeff.reCLM p (positiveCartesianParameterSection w p z).2)) = _
  apply Prod.ext
  · apply RealCoeff.complexCLM_reCLM
    intro n
    rw [positiveCartesianParameterSection_fst]
    split_ifs <;> simp [(hr n).1,hm]
  · apply RealCoeff.complexCLM_reCLM
    intro n
    rw [positiveCartesianParameterSection_snd]
    simp [(hr n).2]

/-- Real normalized parameters retain every native Cartesian coordinate
and the literal signed mean. -/
theorem positiveCartesianRealParameters_injective_on_real
    (z v : PositiveCartesianTarget w p)
    (hz : ∀ n, (z.1.1.val.val n).im = 0 ∧ (z.1.2.val.val n).im = 0) (hzm : z.2.im = 0)
    (hv : ∀ n, (v.1.1.val.val n).im = 0 ∧ (v.1.2.val.val n).im = 0) (hvm : v.2.im = 0)
    (he : positiveCartesianRealParameters w p z = positiveCartesianRealParameters w p v) : z = v := by
  have hh := congrArg (fun a => positiveCartesianParameterMap w p
    (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) a)) he
  simpa only [complex_positiveCartesianRealParameters w p z hz hzm,
    complex_positiveCartesianRealParameters w p v hv hvm,positiveCartesianParameterMap_section] using hh

/-- Nonpositive nonzero indices carry no normalized Cartesian variables. -/
theorem positiveCartesianRealParameters_negative (z : PositiveCartesianTarget w p) (k : ℤ) (hk : k < 0) :
    (positiveCartesianRealParameters w p z).1 k = 0 ∧
    (positiveCartesianRealParameters w p z).2 k = 0 := by
  rw [positiveCartesianRealParameters_fst,positiveCartesianRealParameters_snd,
    z.1.1.property k hk.le,z.1.2.property k hk.le]
  simp [ne_of_lt hk]

/-- The zero head is exactly the signed mean and a zero second entry. -/
theorem positiveCartesianRealParameters_zero (z : PositiveCartesianTarget w p) :
    (positiveCartesianRealParameters w p z).1 0 = z.2.re ∧
    (positiveCartesianRealParameters w p z).2 0 = 0 := by
  rw [positiveCartesianRealParameters_fst,positiveCartesianRealParameters_snd,
    z.1.1.property 0 le_rfl,z.1.2.property 0 le_rfl]
  simp

end NLS.WeightedCoeff
