import NLS.KdV.HillProductCoordinateBounds
import NLS.KdV.HillProductJointPeriods
import NLS.ComplexAnalysis.PairedPoleNormalizedFactor

/-! The balanced Hill factor removes BOTH omitted frequencies. Its
midpoint normalization retains the actual regular quotient, and its
period is an exact nonzero-index rescaling of the original weighted
Hill period, with the literal one-over-two-pi normalization. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillBalancedMidpointRegularFactor (n m : ℕ+) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) : ℂ → ℂ :=
  pairedPoleNormalizedFactor (hillIndependentFrequency (c,d) ((n:ℕ):ℤ))
    (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ))
    (fun z => sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (z,(hillIndependentFrequencyDisplacement (c,d),ψ)))

theorem hillBalancedMidpointRegularFactor_midpoint (n m : ℕ+) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2)
    (hminus : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) ≠ 0)
    (hplus : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) ≠ 0) :
    hillBalancedMidpointRegularFactor n m c d ψ (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)) =
      sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
        (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ),(hillIndependentFrequencyDisplacement (c,d),ψ)) :=
  pairedPoleNormalizedFactor_midpoint _ _ _ hminus hplus

theorem hillWeightedProductIntegrand_eq_balanced_gap_factor (n m : ℕ+) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ)
    (hminus : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z ≠ 0)
    (hplus : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z ≠ 0) :
    (2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*hillEnergyProductPeriodIntegrand n c ψ (z,d) =
      ((hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z)*
        ((I*(Real.pi:ℂ)^2*(((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)/
          (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)^2-z^2))*
          sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
            (z,(hillIndependentFrequencyDisplacement (c,d),ψ))) := by
  rw [hillWeightedProductIntegrand_independent_candidate n m c d ψ z hz hplus]
  have hg := sourcePsiContourIntegrandJoint_eq_gap_factor (by norm_num) (by norm_num)
    ((n:ℕ):ℤ) ((m:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)) ψ z hz (sub_ne_zero.mp hminus).symm
  change sourcePsiCandidate ((n:ℕ):ℤ) (z,hillIndependentFrequencyDisplacement (c,d))/sourceCanonicalRoot (by norm_num) (by norm_num) ψ z =
    ((hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z)*
      sourcePsiGapRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ) (hillIndependentFrequencyDisplacement (c,d)) ψ z at hg
  simp only [mul_div_assoc]
  rw [hg]
  unfold sourcePsiGapRegularFactor
  change _ = _
  have hquad : hillIndependentFrequency (c,d) ((n:ℕ):ℤ)^2-z^2 =
      (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z)*(hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z) := by ring
  rw [hquad]
  change _ = _
  have hstd := sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z (hz _)
  dsimp only [hillIndependentFrequency] at hminus hplus ⊢
  field_simp [hminus,hplus,hstd]
  ring

theorem hillBalancedMidpointRegularFactor_period (n m : ℕ+) (hmn : m ≠ n) (c : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) (a : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere a R ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) ψ)
    (hminus : ∀ z ∈ sphere a R, hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z ≠ 0)
    (hplus : ∀ z ∈ sphere a R, hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z ≠ 0) :
    (∮ z in C(a,R), ((hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)/
      sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z)*hillBalancedMidpointRegularFactor n m c d ψ z) =
      ((hillIndependentFrequency (c,d) ((n:ℕ):ℤ)^2-
        (sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ))^2)/
          (I*(Real.pi:ℂ)^2*(((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)))*
        (hillPeriodEquationWeight n m*hillEnergyProductJointPeriod n a R (d,(c,ψ))) := by
  let β := hillIndependentFrequency (c,d) ((n:ℕ):ℤ)
  let τ := sourceStandardRootMidpoint (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)
  let K : ℂ := I*(Real.pi:ℂ)^2*(((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)
  let A : ℂ := (β^2-τ^2)/K
  have hnm : (((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2) ≠ 0 := by
    rw [show (((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2) = (((n:ℕ):ℂ)-((m:ℕ):ℂ))*(((n:ℕ):ℂ)+((m:ℕ):ℂ)) by ring]
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro he
      apply hmn
      apply Subtype.ext
      exact Nat.cast_injective he.symm
    · exact_mod_cast (show (n:ℕ)+(m:ℕ) ≠ 0 by have := n.pos; omega)
  have hK : K ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))) hnm
  have heq (z : ℂ) (hz : z ∈ sphere a R) :
      ((hillIndependentFrequency (c,d) ((m:ℕ):ℤ)-z)/sourceStandardRoot (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ) z)*
        hillBalancedMidpointRegularFactor n m c d ψ z =
      A*((2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*hillEnergyProductPeriodIntegrand n c ψ (z,d)) := by
    rw [hillWeightedProductIntegrand_eq_balanced_gap_factor n m c d ψ z (hcircle hz) (hminus z hz) (hplus z hz)]
    rw [hillBalancedMidpointRegularFactor,pairedPoleNormalizedFactor_eq_quadratic]
    change _ = A*(_*((K/(β^2-z^2))*_))
    dsimp only [A,β,τ]
    field_simp [hK]
  calc
    _ = ∮ z in C(a,R), A*((2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*hillEnergyProductPeriodIntegrand n c ψ (z,d)) :=
      circleIntegral.integral_congr hR heq
    _ = A*((2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*(∮ z in C(a,R),hillEnergyProductPeriodIntegrand n c ψ (z,d))) := by
      rw [circleIntegral.integral_const_mul,circleIntegral.integral_const_mul]
    _ = _ := by
      change A*((2*Real.pi:ℂ)⁻¹*hillPeriodEquationWeight n m*(∮ z in C(a,R),hillEnergyProductPeriodIntegrand n c ψ (z,d))) =
        A*(hillPeriodEquationWeight n m*((2*Real.pi:ℂ)⁻¹*(∮ z in C(a,R),hillEnergyProductPeriodIntegrand n c ψ (z,d))))
      ring

end NLS.KdV
