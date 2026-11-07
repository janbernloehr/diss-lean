import NLS.KdV.HillHalfPotentialBase
import NLS.KdV.HillNormalizedInverse

/-! Exact normalization of the ORIGINAL native Hill pencil on the ENTIRE
H1 domain and H-minus-one base, with its ACTUAL rough-potential matrix. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The two real positive half-denominators square to the exact complex reciprocal norm. -/
theorem hillHalfDenominatorRaw_mul_self (z : ℂ) (k : ℤ) :
    hillHalfDenominatorRaw z k*hillHalfDenominatorRaw z k = (‖z-(freeHillValue k:ℂ)‖:ℂ)⁻¹ := by
  unfold hillHalfDenominatorRaw
  rw [← Complex.ofReal_mul,← pow_two,inv_pow,Real.sq_sqrt (norm_nonneg _),Complex.ofReal_inv]

/-- The exact normalized free source symbol, including both resonant modes. -/
theorem hillHalfDenominatorRaw_free_phase (z : ℂ) (k : ℤ) :
    hillHalfDenominatorRaw z k*(z-(freeHillValue k:ℂ))*hillHalfDenominatorRaw z k = hillPhaseRaw z k := by
  calc
    _ = (z-(freeHillValue k:ℂ))*(hillHalfDenominatorRaw z k*hillHalfDenominatorRaw z k) := by ring
    _ = _ := by rw [hillHalfDenominatorRaw_mul_self];rfl

/-- The exact ORIGINAL native-pencil identity B(lambda*J-A)D=I-S on EVERY
l2 vector, without finite-mode truncation or a supplied factorization. -/
theorem hillNormalizedPencil_apply (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (a : Coeff 2) :
    hillHalfFromBase z
      ((z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q))
        (hillHalfToH1 z a)) = (hillNormalizedPhase z-hillHalfSandwich r q z) a := by
  ext k
  rw [hillHalfFromBase_coefficient n hn z hz]
  change hillHalfDenominatorRaw z k*
    (z*(singularHillDomainInclusion (hillHalfToH1 z a)).val (mode (-k))-
      (singularHillOperator (hillHalfPotentialBase r hr1 q) (hillHalfToH1 z a)).val (mode (-k))) =
    hillPhaseSymbol z k*a k-hillHalfSandwich r q z a k
  rw [singularHillDomainInclusion_coefficient,singularHillOperator_coefficient,
    hillHalfToH1_coefficient n hn z hz,hillPhaseSymbol_apply,
    hillHalfSandwich_apply r hr hr1 q n hn hlog z hz]
  have hsum : hillHalfDenominatorRaw z k*(∑' m : ℤ,
      (hillHalfPotentialBase r hr1 q).val (mode (-(k-m)))*
        (hillHalfToH1 z a).val (mode (-m))) = ∑' m : ℤ,
      q.val (k-m)*hillHalfDenominatorRaw z k*hillHalfDenominatorRaw z m*a m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [hillHalfPotentialBase_coefficient,hillHalfToH1_coefficient n hn z hz]
    ring
  calc
    _ = (hillHalfDenominatorRaw z k*(z-(freeHillValue k:ℂ))*hillHalfDenominatorRaw z k)*a k-
        hillHalfDenominatorRaw z k*(∑' m : ℤ,
          (hillHalfPotentialBase r hr1 q).val (mode (-(k-m)))*
            (hillHalfToH1 z a).val (mode (-m))) := by ring
    _ = _ := by rw [hillHalfDenominatorRaw_free_phase,hsum]

/-- The genuine bounded-operator factorization on the FULL native spaces. -/
theorem hillNormalizedPencil_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) :
    (hillHalfFromBase z).comp
      ((z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q)).comp
        (hillHalfToH1 z)) = hillNormalizedPhase z-hillHalfSandwich r q z := by
  apply ContinuousLinearMap.ext
  exact hillNormalizedPencil_apply r hr hr1 q n hn hlog z hz

end NLS.KdV
