import NLS.KdV.HillPrimitiveMomentAllIndexBound
import NLS.SequenceSpaces.WeightedMomentSeriesRealization
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! Actual literal moment sums in the inverse-index weighted lp space.
The full matrix bound constructs membership, with exact raw coefficients. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def centeredSecondMomentSequence (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (q : PeriodOneHminusOne) : WeightedCoeff (Weight.signedSobolev (-1)) p :=
  WeightedCoeff.ofFunctionOrZero (Weight.signedSobolev (-1)) p
    (positiveScalarExtension (fun n => P.centeredSecondMomentSeries W n q))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_weighted_centeredSecondMomentSeries (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P)
    (hfull : ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (hp : 1 < p) (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    ∃ b : WeightedCoeff (Weight.signedSobolev (-1)) p,
      (∀ k, b.val k=positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n q) k) ∧
      ‖b‖ ≤ (2*Real.pi*D.constant)*(1+3*‖Coeff.puncturedLattice p hp‖)*
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q)‖^2 := by
  have hC := D.constant_pos
  apply Coeff.exists_weighted_positive_moment_series hp
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q))
    (fun n m => P.centeredMoment D.ambient n m 1 q) (2*Real.pi*D.constant) (by positivity)
  intro n m
  have he (z : ℂ) : ‖z‖=2*Real.pi*‖(2*Real.pi:ℂ)⁻¹*z‖ := by
    simp only [norm_mul,norm_inv,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    field_simp
  rw [he (P.centeredMoment D.ambient n m 1 q)]
  have hb := mul_le_mul_of_nonneg_left (hfull q hq n m) (by positivity : 0 ≤ 2*Real.pi)
  simpa only [mul_assoc] using hb

theorem centeredSecondMomentSequence_bound_and_coefficients (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P)
    (hfull : ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (hp : 1 < p) (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    ‖P.centeredSecondMomentSequence D.ambient p q‖ ≤
        (2*Real.pi*D.constant)*(1+3*‖Coeff.puncturedLattice p hp‖)*
          ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q)‖^2 ∧
      ∀ k, (P.centeredSecondMomentSequence D.ambient p q).val k=
        positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n q) k := by
  obtain ⟨b,hb,hn⟩ := P.exists_weighted_centeredSecondMomentSeries D hfull hp q hq
  rw [centeredSecondMomentSequence,WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ b hb]
  exact ⟨hn,hb⟩

end NLS.KdV.HillProductEquationPatch
