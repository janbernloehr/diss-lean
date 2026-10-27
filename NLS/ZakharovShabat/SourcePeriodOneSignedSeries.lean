import NLS.SequenceSpaces.PairNorm
import NLS.SequenceSpaces.Reflection
import NLS.Fourier.PeriodicFourierLebesgueEndpoints

/-! # The signed period-one expansion used in Lemma 4.3

The input carrier consists of the original periodic smooth-test distributions.
For finite p its pair norm is exactly the printed component-sum norm. The
signed Fourier coordinates reverse the first component and are isometric.
The full series converges in this original norm, and each term is identified
with the printed physical exponential modes. The auxiliary WithLp product at
infinity is not the dissertation's coupled infinity norm.
-/
noncomputable section
open scoped ENNReal
open NLS NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original periodic distribution pairs with the finite-exponent source norm. -/
abbrev SourcePeriodicPair (L : ℝ) [Fact (0 < L)] (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  WithLp p (PeriodicFourierLebesgue L Weight.one p ×
    PeriodicFourierLebesgue L Weight.one p)

/-- Raw normalized Fourier coordinates at the actual physical period. -/
def sourcePeriodicPairCoefficients (L : ℝ) [Fact (0 < L)] :
    SourcePeriodicPair L p ≃ₗᵢ[ℂ] CoeffPair p :=
  (PeriodicFourierLebesgue.unweightedCoefficients (L := L) p).withLpProdCongr p
    (PeriodicFourierLebesgue.unweightedCoefficients (L := L) p)

theorem sourcePeriodicPairCoefficients_fst (L : ℝ) [Fact (0 < L)]
    (u : SourcePeriodicPair L p) (n : ℤ) :
    (sourcePeriodicPairCoefficients L u).fst n = u.fst.val (mode (-n)) :=
  PeriodicFourierLebesgue.unweightedCoefficients_apply p u.fst n

theorem sourcePeriodicPairCoefficients_snd (L : ℝ) [Fact (0 < L)]
    (u : SourcePeriodicPair L p) (n : ℤ) :
    (sourcePeriodicPairCoefficients L u).snd n = u.snd.val (mode (-n)) :=
  PeriodicFourierLebesgue.unweightedCoefficients_apply p u.snd n

/-- The printed signed coordinates on the original period-one distributions. -/
def sourceUnitPeriodSignedCoefficients : SourcePeriodicPair 1 p ≃ₗᵢ[ℂ] CoeffPair p :=
  ((PeriodicFourierLebesgue.unweightedCoefficients (L := 1) p).trans
    Coeff.reflection).withLpProdCongr p
    (PeriodicFourierLebesgue.unweightedCoefficients (L := 1) p)

theorem sourceUnitPeriodSignedCoefficients_fst (u : SourcePeriodicPair 1 p) (n : ℤ) :
    (sourceUnitPeriodSignedCoefficients u).fst n = u.fst.val (mode n) := by
  change Coeff.reflection
    (PeriodicFourierLebesgue.unweightedCoefficients p u.fst) n = _
  simp

theorem sourceUnitPeriodSignedCoefficients_snd (u : SourcePeriodicPair 1 p) (n : ℤ) :
    (sourceUnitPeriodSignedCoefficients u).snd n = u.snd.val (mode (-n)) := by
  exact PeriodicFourierLebesgue.unweightedCoefficients_apply p u.snd n

theorem norm_sourceUnitPeriodSignedCoefficients (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    ‖u‖ = (∑' n : ℤ,
      (‖u.fst.val (mode n)‖ ^ p.toReal +
        ‖u.snd.val (mode (-n))‖ ^ p.toReal)) ^ (1 / p.toReal) := by
  rw [← sourceUnitPeriodSignedCoefficients.norm_map u, CoeffPair.norm_eq_tsum_rpow hp]
  simp only [sourceUnitPeriodSignedCoefficients_fst, sourceUnitPeriodSignedCoefficients_snd]

theorem sourcePeriodicPairCoefficients_eq_signed (u : SourcePeriodicPair 1 p) :
    sourcePeriodicPairCoefficients 1 u = WithLp.toLp p
      (Coeff.reflection (sourceUnitPeriodSignedCoefficients u).fst, (sourceUnitPeriodSignedCoefficients u).snd) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change PeriodicFourierLebesgue.unweightedCoefficients p u.fst n =
      Coeff.reflection (sourceUnitPeriodSignedCoefficients u).fst n
    simp [sourceUnitPeriodSignedCoefficients_fst]
  · rfl


/-- The actual signed pair of modes with arbitrary complex amplitudes. -/
def sourceUnitPeriodSignedMode (n : ℤ) (a b : ℂ) : SourcePeriodicPair 1 p :=
  sourceUnitPeriodSignedCoefficients.symm (WithLp.toLp p (lp.single p n a, lp.single p n b))

theorem sourceUnitPeriodSignedMode_physical (n : ℤ) (a b : ℂ) :
    (sourceUnitPeriodSignedMode (p := p) n a b).fst.val =
        Distribution.ofContinuous (a • (fourier (-n) : C(AddCircle (1 : ℝ), ℂ))) ∧
      (sourceUnitPeriodSignedMode (p := p) n a b).snd.val =
        Distribution.ofContinuous (b • (fourier n : C(AddCircle (1 : ℝ), ℂ))) := by
  have he := sourceUnitPeriodSignedCoefficients.apply_symm_apply (WithLp.toLp p (lp.single p n a, lp.single p n b))
  constructor
  · apply Distribution.ext_coefficients
    intro k
    have hk := congrArg (fun v : CoeffPair p => v.fst (-k)) he
    change (sourceUnitPeriodSignedCoefficients (sourceUnitPeriodSignedMode n a b)).fst (-k) = (lp.single p n a : Coeff p) (-k) at hk
    rw [sourceUnitPeriodSignedCoefficients_fst] at hk
    rw [hk, Distribution.ofContinuous_coefficient, ContinuousMap.coe_smul,
      fourierCoeff.const_smul, fourierCoeff_fourier]
    simp [lp.single_apply, Pi.single_apply, eq_neg_iff_add_eq_zero,
      add_comm, eq_comm]
  · apply Distribution.ext_coefficients
    intro k
    have hk := congrArg (fun v : CoeffPair p => v.snd k) he
    change (sourceUnitPeriodSignedCoefficients (sourceUnitPeriodSignedMode n a b)).snd k = (lp.single p n b : Coeff p) k at hk
    rw [sourceUnitPeriodSignedCoefficients_snd] at hk
    rw [hk, Distribution.ofContinuous_coefficient, ContinuousMap.coe_smul,
      fourierCoeff.const_smul, fourierCoeff_fourier]
    simp [lp.single_apply, Pi.single_apply, eq_comm]

/-- The full printed signed series converges in the exact finite-p source norm. -/
theorem hasSum_sourceUnitPeriodSignedModes (hp : p ≠ ⊤) (u : SourcePeriodicPair 1 p) :
    HasSum (fun n : ℤ => sourceUnitPeriodSignedMode n
      ((sourceUnitPeriodSignedCoefficients u).fst n) ((sourceUnitPeriodSignedCoefficients u).snd n)) u := by
  let L : (Coeff p × Coeff p) →L[ℂ] SourcePeriodicPair 1 p :=
    sourceUnitPeriodSignedCoefficients.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (CoeffPair.toMax p).symm.toContinuousLinearMap
  have h := L.hasSum ((lp.hasSum_single hp (sourceUnitPeriodSignedCoefficients u).fst).prodMk
    (lp.hasSum_single hp (sourceUnitPeriodSignedCoefficients u).snd))
  convert h using 1
  · rfl
  · exact (sourceUnitPeriodSignedCoefficients.symm_apply_apply u).symm

/-- Unit-period physical modes are precisely the source's even-index period-two waves. -/
theorem sourceUnitPeriodMode_eq_evenWave (n : ℤ) (x : ℝ) :
    (fourier n : C(AddCircle (1 : ℝ), ℂ)) (x : AddCircle (1 : ℝ)) = wave (2*n) x := by
  rw [fourier_coe_apply]
  unfold wave
  congr 1
  push_cast
  ring

end NLS.ZakharovShabat
