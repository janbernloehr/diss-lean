import NLS.Fourier.RudinShapiro
import NLS.Fourier.CircleHausdorffYoungSynthesis
import NLS.Fourier.PeriodicL1Uniqueness

/-!
# Finite coefficient data of the Rudin–Shapiro polynomials

The actual Fourier coefficients form a finitely supported sequence with
exact support [0, 2^n) and finite p-norm (2^n)^(1/p). Finite synthesis
recovers the polynomial in every Banach Lᑫ quotient, including infinity.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- The actual finite Fourier coefficient sequence of the first polynomial. -/
def rudinShapiroCoefficients (n : ℕ) : ℤ →₀ ℂ :=
  Finsupp.onFinset (Finset.Ico (0:ℤ) (2^n:ℕ)) (fourierCoeff (rudinShapiroPair (L := L) n).1) (by
    intro k hk
    by_contra hn
    simp only [Finset.mem_Ico] at hn
    apply hk
    exact norm_eq_zero.mp (by simpa only [if_neg hn] using (rudinShapiro_coeff_norm (L := L) n k).1))

theorem rudinShapiroCoefficients_apply (n : ℕ) (k : ℤ) :
    rudinShapiroCoefficients (L := L) n k = fourierCoeff (rudinShapiroPair (L := L) n).1 k := by
  rfl

/-- The support contains every index in the block and no others. -/
theorem rudinShapiroCoefficients_support (n : ℕ) :
    (rudinShapiroCoefficients (L := L) n).support = Finset.Ico (0:ℤ) (2^n:ℕ) := by
  ext k
  rw [Finsupp.mem_support_iff,rudinShapiroCoefficients_apply,← norm_ne_zero_iff,
    (rudinShapiro_coeff_norm n k).1,Finset.mem_Ico]
  split_ifs <;> simp_all

/-- Finite synthesis recovers the polynomial in every Banach Lᑫ quotient. -/
theorem finiteCircleSynthesis_rudinShapiro {q : ℝ≥0∞} [Fact (1 ≤ q)] (n : ℕ) :
    finiteCircleSynthesis (q := q) (rudinShapiroCoefficients (L := L) n) =
      ContinuousMap.toLp q AddCircle.haarAddCircle ℂ (rudinShapiroPair (L := L) n).1 := by
  apply circleLp_fourierCoeff_injective
  funext k
  dsimp only
  rw [finiteCircleSynthesis_coefficient,rudinShapiroCoefficients_apply,
    fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _)]

/-- The exact finite p-norm of a block of 2^n unit coefficients. -/
theorem norm_rudinShapiroCoefficients {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (n : ℕ) :
    ‖Coeff.ofFinsupp (p := p) (rudinShapiroCoefficients (L := L) n)‖ =
      ((2:ℝ)^n)^(1/p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  simp only [Coeff.ofFinsupp_apply,rudinShapiroCoefficients_apply]
  congr 1
  rw [tsum_eq_sum (s := Finset.Ico (0:ℤ) (2^n:ℕ))]
  · calc
      _ = ∑ _k ∈ Finset.Ico (0:ℤ) (2^n:ℕ), (1:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [(rudinShapiro_coeff_norm n k).1,if_pos (Finset.mem_Ico.mp hk),Real.one_rpow]
      _ = _ := by
        simp only [Finset.sum_const,Int.card_Ico,sub_zero,nsmul_eq_mul,mul_one]
        exact_mod_cast Int.toNat_of_nonneg (show (0:ℤ) ≤ 2^n by positivity)
  · intro k hk
    rw [(rudinShapiro_coeff_norm n k).1,if_neg (by simpa only [Finset.mem_Ico] using hk),Real.zero_rpow hp.ne']

end NLS.Fourier
