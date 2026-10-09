import NLS.Fourier.PeriodOneH1Norm
import NLS.ZakharovShabat.SourcePiSobolevCoordinates
import NLS.ZakharovShabat.IntervalH1OperatorBound

/-! # The integral H1 norm is bounded by the exact source Fourier norm

The source weight is 1+|2*pi*n| and the pair norm is Hilbert. The comparison
has constant one. It uses unit-period Parseval, not a norm-equivalence bound
for the ambient period-two realization.
-/
noncomputable section
open Set MeasureTheory
open NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The original period-one H1 potential reconstructed from its coefficients. -/
def sourcePeriodicH1Potential (a : ScalarDomain 2 × ScalarDomain 2) (s : ℝ) : ℂ × ℂ :=
  (periodOneSobolevSynthesis a.1 (s : AddCircle (2 : ℝ)),
    periodOneSobolevSynthesis a.2 (s : AddCircle (2 : ℝ)))

theorem continuous_sourcePeriodicH1Potential (a : ScalarDomain 2 × ScalarDomain 2) :
    Continuous (sourcePeriodicH1Potential a) :=
  (continuous_periodOneSobolevSynthesis a.1).prodMk (continuous_periodOneSobolevSynthesis a.2)

theorem periodic_sourcePeriodicH1Potential (a : ScalarDomain 2 × ScalarDomain 2) :
    Function.Periodic (sourcePeriodicH1Potential a) 1 := by
  intro s
  exact Prod.ext (periodOneSobolevSynthesis_periodic a.1 s) (periodOneSobolevSynthesis_periodic a.2 s)

theorem memLp_sourcePeriodicH1Potential (a : ScalarDomain 2 × ScalarDomain 2) :
    MemLp (sourcePeriodicH1Potential a) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_two_interval (continuous_periodOneSobolevSynthesis a.1) 0 1 (by norm_num),
    memLp_two_interval (continuous_periodOneSobolevSynthesis a.2) 0 1 (by norm_num)⟩

/-- Reconstruction retains both original unit-period coefficient sequences. -/
theorem sourcePeriodicH1Potential_coefficients (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    periodOneCoefficient (fun s => (sourcePeriodicH1Potential a s).1) n = a.1.val n ∧
      periodOneCoefficient (fun s => (sourcePeriodicH1Potential a s).2) n = a.2.val n := by
  exact ⟨periodOneCoefficient_periodOneSobolevSynthesis a.1 n,
    periodOneCoefficient_periodOneSobolevSynthesis a.2 n⟩

/-- The periodic representative recovers the existing classical H1 curve on [0,1]. -/
theorem sourcePeriodicH1Potential_eq_classical (a : ScalarDomain 2 × ScalarDomain 2)
    (t : Icc (0 : ℝ) 1) :
    sourcePeriodicH1Potential a t = NLS.LinearVolterra.extend
      (classicalSobolevPotential (Coeff.periodDoubleSobolev a.1,Coeff.periodDoubleSobolev a.2)) t := by
  rw [NLS.LinearVolterra.extend_coe]
  apply Prod.ext <;> simp only [sourcePeriodicH1Potential,classicalSobolevPotential,
    sobolevUnitCurve,ContinuousMap.coe_mk,periodOneSobolevSynthesis_eq]

private theorem hasSum_coeff_sq (a : Coeff 2) : HasSum (fun n => ‖a n‖^2) (‖a‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) a

/-- The scalar graph energy is bounded by the exact physical Fourier weight. -/
theorem graphEnergy_le_sourcePiSobolev_one (a : ScalarDomain 2) :
    ‖scalarInclusion a‖^2+‖periodOneDerivative a‖^2 ≤ ‖sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a,0)).1‖^2 := by
  apply hasSum_le _ ((hasSum_coeff_sq (scalarInclusion a)).add (hasSum_coeff_sq (periodOneDerivative a)))
    (hasSum_coeff_sq (sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a,0)).1))
  intro n
  dsimp only
  have hw : ‖sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a,0)).1 n‖^2 =
      (1+2*Real.pi*|(n : ℝ)|)^2*‖a.val n‖^2 := by
    have hcoef : sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a,0)).1 n =
        ((1+2*Real.pi*|(n : ℝ)| : ℝ) : ℂ)*a.val n := by
      rw [sourcePiSobolevScalar_apply]
      have ha : (higherSobolevSourceOneEquiv (a,0)).1.val n = a.val n := by
        change 1*a.val n = a.val n
        exact one_mul _
      rw [ha]
      congr 1
      simp [SpectralWeight.piSobolev_apply,abs_mul,Real.pi_pos.le,mul_comm,mul_left_comm]
    rw [hcoef,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity),mul_pow]
  have hd : ‖periodOneDerivative a n‖^2 = (2*Real.pi*|(n : ℝ)|)^2*‖a.val n‖^2 := by
    simp [periodOneDerivative_apply,Complex.norm_intCast,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,mul_pow]
  rw [hw,hd,scalarInclusion_apply]
  nlinarith [mul_nonneg (by positivity : 0 ≤ 2*Real.pi*|(n : ℝ)|) (sq_nonneg ‖a.val n‖)]

/-- Exact graph energy of both physical components. -/
theorem intervalPairH1Norm_sourcePeriodic_sq (a : ScalarDomain 2 × ScalarDomain 2) :
    intervalPairH1Norm (sourcePeriodicH1Potential a) 1 ^ 2 =
      (‖scalarInclusion a.1‖^2+‖periodOneDerivative a.1‖^2)+
        (‖scalarInclusion a.2‖^2+‖periodOneDerivative a.2‖^2) := by
  rw [intervalPairH1Norm,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact congrArg₂ (· + ·) (intervalH1Norm_sq_periodOneSobolevSynthesis a.1)
    (intervalH1Norm_sq_periodOneSobolevSynthesis a.2)

/-- Constant-one comparison with the exact Chapter 5 Hilbert Fourier norm. -/
theorem intervalPairH1Norm_sourcePeriodic_le (a : ScalarDomain 2 × ScalarDomain 2) :
    intervalPairH1Norm (sourcePeriodicH1Potential a) 1 ≤ ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖ := by
  have h := add_le_add (graphEnergy_le_sourcePiSobolev_one a.1) (graphEnergy_le_sourcePiSobolev_one a.2)
  rw [← intervalPairH1Norm_sourcePeriodic_sq] at h
  have he : ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖^2 =
      ‖sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a.1,0)).1‖^2+‖sourcePiSobolevScalar 1 1 le_rfl (higherSobolevSourceOneEquiv (a.2,0)).1‖^2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  rw [← he] at h
  exact (sq_le_sq₀ (intervalPairH1Norm_nonneg _ _) (norm_nonneg _)).mp h

/-- The right-hand norm is exactly the printed weighted Hilbert coefficient norm. -/
theorem sourcePeriodicH1_fourierNorm_sq (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖sourcePiSobolevCoordinates 1 1 le_rfl (higherSobolevSourceOneEquiv a)‖^2 =
      ∑' n : ℤ, (1+|((2*n : ℤ) : ℝ)*Real.pi|)^2*(‖a.1.val n‖^2+‖a.2.val n‖^2) := by
  rw [sourcePiSobolevCoordinates_norm_sq]
  apply tsum_congr
  intro n
  change (1+|((2*n : ℤ) : ℝ)*Real.pi|)^(2*1)*(‖1*a.1.val n‖^2+‖1*a.2.val n‖^2) = _
  simp only [mul_one,one_mul]

end NLS.ZakharovShabat
