import NLS.KdV.HillPlacedEnergySeparation

/-! Off-diagonal filled columns have the actual quadratic interaction
kernel. The selected energy width carries the inverse-index row weight. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillWeightedColumnGapNumerator_cross (n m r : ℕ+) (hmn : m ≠ n) (hrn : r ≠ n)
    (c : ℂ) (ψ : CoeffPair 2) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ)
    (hrz : hillEnergySequenceZero r d-(z^2-c) ≠ 0) :
    hillPeriodEquationWeight n m*hillProductColumnGapNumerator n r c ψ ((m:ℕ):ℤ) d z =
      ((hillEnergySequenceZero m d-(z^2-c))/(m:ℕ))*
        (((r:ℕ):ℂ)/(hillEnergySequenceZero r d-(z^2-c)))*
          (hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z) := by
  have h := hillEnergyProductCoordinateDerivative_cross n m r hmn hrn (z^2-c) d
  have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  unfold hillProductColumnGapNumerator
  rw [div_mul_eq_mul_div]
  have he := congrArg (fun w : ℂ => hillPeriodEquationWeight n m*z*w/
    sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z) h
  apply mul_left_cancel₀ (mul_ne_zero hm hrz)
  field_simp [hm,hrz] at *
  linear_combination he

theorem hillWeightedColumnGapNumerator_off_diagonal_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m r : ℕ+) (hmn : m ≠ n) (hrn : r ≠ n) (hrm : r ≠ m)
    (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ)))
    (hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ))
    (Q B : ℝ) (hB : 0 ≤ B)
    (hq : ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q)
    (hgap : ‖(hillEnergySequenceZero m d-(z^2-c))/(m:ℕ)‖ ≤ B) :
    ‖hillPeriodEquationWeight n m*hillProductColumnGapNumerator n r c ψ ((m:ℕ):ℤ) d z‖ ≤
      B*(2*Real.pi^5*C^5*Q)*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖ := by
  have hg := hillWeightedColumnGapNumerator_bound hD ψ c d hplace n m hmn z hz hother Q hq
  have hk := hillPlacedEnergy_inverse_index_kernel_bound hD (c,d) hplace m r hrm z hz
  rw [hillWeightedColumnGapNumerator_cross n m r hmn hrn c ψ d z
    (hillPlacedEnergy_difference_ne_zero hD (c,d) hplace m r hrm z hz),norm_mul,norm_mul]
  have hc : 0 ≤ C := zero_le_one.trans hD.one_le
  calc
    _ ≤ (B*(Real.pi^2*C^2*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖))*(2*Real.pi^3*C^3*Q) :=
      mul_le_mul (mul_le_mul hgap hk (norm_nonneg _) hB) hg (norm_nonneg _) (by positivity)
    _ = _ := by ring

end NLS.KdV
