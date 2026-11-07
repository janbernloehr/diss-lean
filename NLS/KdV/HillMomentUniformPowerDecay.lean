import NLS.KdV.HillMomentGapDecay
import NLS.KdV.HillPrimitiveMomentSeriesNeighborhood
import NLS.SequenceSpaces.ReciprocalMomentRowDecay

/-! Uniform decay of the genuine second-moment series from the original
Hill-gap power bound. One decaying majorant precedes the varying source. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem exists_uniform_centeredMomentSeries_power_decay (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (r : ℝ) (hr1 : r < 1/2)
    (a C : ℝ) (ha : 0 < a)
    (hfull : ∀ q ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 q‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)‖^2*
          Coeff.positiveMomentKernel n m) :
    ∃ B : ℤ → ℝ, (∀ n, 0 ≤ B n) ∧ Tendsto B cofinite (𝓝 0) ∧
      ∀ q ∈ D.source,
        (∀ m : ℕ+, a*(m:ℝ) ≤
          ‖sourceStandardRootMidpoint (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)‖) →
        (∀ m : ℕ+, ‖hillHminusCanonicalGapSquare m q‖ ≤ C^2*(1+(m:ℝ))^(2*r)) →
        ∀ n : ℕ+, ‖P.centeredSecondMomentSeries D.ambient n q‖ ≤ B (n:ℤ) := by
  let K : ℝ := D.constant*(C^2/(2*a^2))
  have hK : 0 ≤ K := mul_nonneg D.constant_pos.le (by positivity)
  obtain ⟨B,hB,hlim,hbound⟩ := Coeff.exists_uniform_polynomial_moment_row_decay
    (1-2*r) (by linarith) K hK
  refine ⟨fun n => (2*Real.pi)*B n,fun n => mul_nonneg (by positivity) (hB n),?_,?_⟩
  · simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  · intro q hq hmid hgap n
    have hqP : q ∈ P.source := (D.subset hq).1
    have hu (m : ℕ+) : ‖P.normalizedWeightedSecondMoment D.ambient n q m‖ ≤
        K/(1+(m:ℝ))^(1-2*r)*Coeff.positiveMomentKernel n m := by
      have hg := P.weighted_dirac_gap_power_bound q hqP m r a C ha (hmid m) (hgap m)
      have hn : (0:ℝ)≤m := by positivity
      have hker : 0 ≤ Coeff.positiveMomentKernel n m := by
        unfold Coeff.positiveMomentKernel
        split_ifs <;> positivity
      rw [normalizedWeightedSecondMoment,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ (m:ℝ)*(D.constant*
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)‖^2*
              Coeff.positiveMomentKernel n m) := mul_le_mul_of_nonneg_left (hfull q hq n m) hn
        _ = (D.constant*((m:ℝ)*
            ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q) (m:ℤ)‖^2))*
              Coeff.positiveMomentKernel n m := by ring
        _ ≤ (D.constant*((C^2/(2*a^2))/(1+(m:ℝ))^(1-2*r)))*
              Coeff.positiveMomentKernel n m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg D.constant_pos.le) hker
        _ = _ := by dsimp only [K]; ring
    have hb := (hbound (P.normalizedWeightedSecondMoment D.ambient n q) n hu).2
    rw [P.centeredSecondMomentSeries_eq_row_sum D n q hq,centeredSecondMomentRow,
      Coeff.tsum_positiveSummableRealization _ (P.summable_normalizedWeightedSecondMoment D n q hq),norm_mul]
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    exact mul_le_mul_of_nonneg_left hb (by positivity)

end NLS.KdV.HillProductEquationPatch
