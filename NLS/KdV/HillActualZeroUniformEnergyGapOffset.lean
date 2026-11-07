import NLS.KdV.HillActualZeroUniformQuadraticOffset
import NLS.KdV.HillFrequencyScaleBounds
import NLS.KdV.HillQuadraticFrequencyEnergyOffset
import NLS.KdV.HillCanonicalEnergyMidpoints
import NLS.KdV.HillHminusOneCanonicalGapSquares

/-! The ORIGINAL energy-zero minus ORIGINAL energy-midpoint estimate:
one complex native source ball and one constant work BEFORE ALL
numerator and gap indices, including low/collapsed/omitted gaps.
The denominator is the literal original positive gap index. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_common_actual_zero_uniform_squared_energy_gap_offset (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalGapDomain ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+,
        ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n y)-hillHminusCanonicalEnergyMidpoint m y‖ ≤
          C*‖hillHminusCanonicalGapSquare m y‖/(m:ℝ) := by
  obtain ⟨rF,L,hrF,hL,hU,hfreq⟩ := P.exists_common_actual_zero_uniform_quadratic_frequency_offset q hq hr
  obtain ⟨rS,a,B,hrS,ha,hB,hsource,hscale⟩ := P.exists_common_actual_frequency_scale_bounds q hq hr
  obtain ⟨rP,hrP,_,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  let r := min rF (min rS rP)
  have hrpos : 0 < r := lt_min hrF (lt_min hrS hrP)
  have hrf : r ≤ rF := min_le_left _ _
  have hrs : r ≤ rS := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : r ≤ rP := (min_le_right _ _).trans (min_le_right _ _)
  let C := (L*B+1)/(4*a^2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let A := P.parent.parent.miuraBall
  have hsourceA (y : PeriodOneHminusOne) (hy : y ∈ ball q r) : y ∈ A.source :=
    (P.parent.subset (P.subset (hsource (ball_subset_ball hrs hy)))).1
  refine ⟨r,C,hrpos,hC,(fun y hy => ⟨hU (ball_subset_ball hrf hy),mem_iUnion.mpr ⟨A,hsourceA y hy⟩⟩),?_⟩
  intro y hy n m
  by_cases hmn : m = n
  · subst n
    rw [hillHminusCanonicalEnergyMidpoint,sub_self,norm_zero]
    exact div_nonneg (mul_nonneg hC (norm_nonneg _)) (by positivity)
  · let d := hillHminusCanonicalZeroSequence n y
    let c : ℂ := (A.actionBall.shift:ℂ)
    let β := hillIndependentFrequency (c,d) ((m:ℕ):ℤ)
    let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)
    let γ := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi y) ((m:ℕ):ℤ)
    have hper := hperiod y (ball_subset_ball hrp hy) m
    have hmid : hillHminusCanonicalEnergyMidpoint m y = A.energyMidpoint m y :=
      P.canonical_energyMidpoint_eq_local m y hper.1 hper.2
    have henergy : hillEnergySequenceZero m d-A.energyMidpoint m y = β^2-τ^2-γ^2/4 := by
      dsimp only [β]
      rw [hillIndependentFrequency_positive_sq]
      dsimp only [A,HillHminusMiuraGapBall.energyMidpoint,τ,γ,c]
      rw [sourcePeriodicGapDisplacement_apply]
      dsimp only [sourcePsi]
      ring
    have hgap : hillHminusCanonicalGapSquare m y = γ^2*(2*τ)^2 := by
      rw [A.canonical_gapSquare_eq m y (hsourceA y hy)]
      dsimp only [HillHminusMiuraGapBall.gapSquare,HillHminusMiuraGapBall.diracSum,γ,τ,A]
      rw [sourcePeriodicGapDisplacement_apply]
      rfl
    rw [hmid,henergy,hgap]
    exact norm_quadratic_energy_offset_le β τ γ m a B L ha hB hL
      (hfreq y (ball_subset_ball hrf hy) n m hmn)
      (hscale y (ball_subset_ball hrs hy) m).1 ((hscale y (ball_subset_ball hrs hy) m).2 n)

end NLS.KdV.HillProductEquationPatch
