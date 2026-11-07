import NLS.KdV.HillProductColumnFactorization
import NLS.KdV.HillIndependentMultiplierBound

/-! A uniform bound for the regular weighted Hill diagonal column
numerator on entire original closed row discs. It follows from the
proved quotient bound and original separation, before all indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillIndependent_sum_index_ratio_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (n m : ℕ+) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    ‖(((n:ℕ):ℂ)+((m:ℕ):ℂ))/(hillIndependentFrequency t ((n:ℕ):ℤ)+z)‖ ≤ C := by
  have hmn : ((m:ℕ):ℤ) ≠ -((n:ℕ):ℤ) := by
    have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    have hn : 0 < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
    omega
  have hneg : -hillIndependentFrequency t ((n:ℕ):ℤ) ∈ D (-((n:ℕ):ℤ)) := by
    rw [← hillIndependentFrequency_neg]
    exact hplace _
  have hs := (hD.weighted_separation_closure (-((n:ℕ):ℤ)) ((m:ℕ):ℤ) hmn
    (-hillIndependentFrequency t ((n:ℕ):ℤ)) hneg z hz).2
  have he : ((-((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ) = -(((n:ℕ):ℂ)+((m:ℕ):ℂ)) := by push_cast; ring
  rw [he,norm_neg,show -hillIndependentFrequency t ((n:ℕ):ℤ)-z =
    -(hillIndependentFrequency t ((n:ℕ):ℤ)+z) by ring,norm_neg] at hs
  simpa only [norm_div] using hs

theorem hillIndependent_row_index_ratio_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (m : ℕ+) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    ‖((m:ℕ):ℂ)/(hillIndependentFrequency t ((m:ℕ):ℤ)+z)‖ ≤ C := by
  have hs := hillIndependent_sum_index_ratio_bound hD t hplace m m z hz
  have he : ((m:ℕ):ℂ)/(hillIndependentFrequency t ((m:ℕ):ℤ)+z) =
      (1/2:ℂ)*((((m:ℕ):ℂ)+((m:ℕ):ℂ))/(hillIndependentFrequency t ((m:ℕ):ℤ)+z)) := by ring
  rw [he,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat] at *
  have hc : 0 ≤ C := zero_le_one.trans hD.one_le
  nlinarith

theorem hillWeightedColumnGapNumerator_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (n m : ℕ+) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ)))
    (hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ))
    (Q : ℝ)
    (hq : ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ)
      (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q) :
    ‖hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z‖ ≤
      2*Real.pi^3*C^3*Q := by
  let b := hillIndependentFrequencyDisplacement (c,d)
  let bn := hillIndependentFrequency (c,d) ((n:ℕ):ℤ)
  let bm := hillIndependentFrequency (c,d) ((m:ℕ):ℤ)
  let M : ℂ := (Real.pi:ℂ)^2*(((n:ℕ):ℂ)+((m:ℕ):ℂ))/(bn+z)
  let R : ℂ := ((((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)*
    sourcePsiGapRegularFactor (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((m:ℕ):ℤ) b ψ z
  have hmn' : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by
    intro h
    exact hmn (Subtype.ext (Int.ofNat.inj h))
  have hs := hD.weighted_separation_closure ((n:ℕ):ℤ) ((m:ℕ):ℤ) hmn'
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)) (hplace _) z hz
  have hnp := hillIndependent_multiplier_bound hD (c,d) hplace n m z hz
  have hmp := hillIndependent_multiplier_bound hD (c,d) hplace m m z hz
  have ho := sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) ψ z ((m:ℕ):ℤ) hother
  have hc : 0 ≤ C := zero_le_one.trans hD.one_le
  have hR : ‖R‖ ≤ C*Q := by
    simp only [R,sourcePsiGapRegularFactor,norm_mul,norm_div,norm_I,one_mul]
    rw [← mul_div_assoc,mul_div_right_comm]
    exact mul_le_mul hs.2 hq (norm_nonneg _) hc
  have hid : hillPeriodEquationWeight n m*hillProductColumnGapNumerator n m c ψ ((m:ℕ):ℤ) d z =
      (2*Real.pi*Complex.I:ℂ)*(((m:ℕ):ℂ)/(bm+z))*M*R := by
    have hf := hillEnergyProductCoordinateDerivative_frequency_filled n m hmn c d z
    have hn : ((n:ℕ):ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
    have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hmz : bm+z ≠ 0 := hmp.1
    have hnz : bn+z ≠ 0 := hnp.1
    have hnmz : bn-z ≠ 0 := sub_ne_zero.mpr hs.1.symm
    change (bn-z)*(bn+z)*(bm+z)*z*hillEnergyProductCoordinateDerivative n m (z^2-c,d) =
      -((Real.pi:ℂ)*(n:ℕ))^2*(m:ℕ)*jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (z,b) at hf
    change hillPeriodEquationWeight n m*(z*hillEnergyProductCoordinateDerivative n m (z^2-c,d)/
      sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z) =
      (2*Real.pi*Complex.I:ℂ)*(((m:ℕ):ℂ)/(bm+z))*
        ((Real.pi:ℂ)^2*(((n:ℕ):ℂ)+((m:ℕ):ℂ))/(bn+z))*
        (((((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ)*(Complex.I*
          (jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (z,b)/
            sourceStandardRootOmittedProduct (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z)/(bn-z)))
    unfold hillPeriodEquationWeight
    push_cast
    field_simp [ho,hn,hp,hmz,hnz,hnmz]
    simp only [Complex.I_sq]
    linear_combination (((n:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)*hf
  rw [hid,norm_mul,norm_mul,norm_mul]
  have hscalar : ‖(2*Real.pi*Complex.I:ℂ)‖ = 2*Real.pi := by
    simp [Real.norm_of_nonneg Real.pi_pos.le]
  rw [hscalar]
  have hb := hillIndependent_row_index_ratio_bound hD (c,d) hplace m z hz
  have hm : ‖M‖ ≤ Real.pi^2*C := hnp.2
  calc
    _ ≤ (2*Real.pi)*C*(Real.pi^2*C)*(C*Q) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hm
        (norm_nonneg _) (by positivity)) hR (norm_nonneg _) (by positivity)
    _ = _ := by ring

end NLS.KdV
