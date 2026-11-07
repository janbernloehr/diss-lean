import NLS.KdV.HillBalancedGapFrequencies
import NLS.ZakharovShabat.BalancedSingleSpectralProducts
import NLS.ZakharovShabat.RestoredQuadraticProductGrowth
import NLS.ComplexAnalysis.OddEntireProductFactor
import NLS.ComplexAnalysis.QuadraticRestoration

/-! Restoring the omitted real Hill energy zero gives the ACTUAL full
balanced spectral product up to a NONZERO scalar. Its entire quotient
is even and subquadratic on expanding circles. No universal scalar
normalization is inferred from the zero set or growth alone. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_real_hill_restored_product_factor
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (hPne : P ≠ 0) (n : ℕ+) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))))
    (hzeros : ∀ m : ℕ+, m ≠ n → P (σ m:ℂ) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-(c:ℂ)))/(-2*sin z)‖ ≤ ε) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      ((σ n:ℂ)-(z^2-(c:ℂ)))*(2*z*P (z^2-(c:ℂ))) =
        C*entireSingleSpectralProduct (hillBalancedGapFrequency σ c) z := by
  let ρ := hillBalancedGapFrequency σ c
  let H : ℂ → ℂ := fun z => ((σ n:ℂ)-(z^2-(c:ℂ)))*(2*z*P (z^2-(c:ℂ)))
  let G := entireSingleSpectralProduct ρ
  have hρ := memlp_hillBalancedGapFrequency_displacement q hq u c hi hc σ hσ
  have hinj := hillBalancedGapFrequency_injective q hq u c hi hc σ hσ
  have hH : AnalyticOnNhd ℂ H univ := by
    intro z _
    have he : AnalyticAt ℂ (fun w : ℂ => w^2-(c:ℂ)) z := (analyticAt_id.pow 2).sub analyticAt_const
    exact (analyticAt_const.sub he).mul ((analyticAt_const.mul analyticAt_id).mul
      ((hP _ (mem_univ _)).comp (f := fun w : ℂ => w^2-(c:ℂ)) he))
  have hG : AnalyticOnNhd ℂ G univ := analyticOnNhd_entireSingleSpectralProduct (by norm_num) ρ hρ
  have hsimple : ∀ z : ℂ, G z = 0 → deriv G z ≠ 0 :=
    entireSingleSpectralProduct_simple_zeros_of_injective (by norm_num) (by norm_num) ρ hρ hinj
  have hHodd (z : ℂ) : H (-z) = -H z := by dsimp only [H]; rw [neg_sq]; ring
  have hGodd (z : ℂ) : G (-z) = -G z :=
    entireSingleSpectralProduct_neg_of_balanced (by norm_num) ρ hρ
      (hillBalancedGapFrequency_zero σ c) (hillBalancedGapFrequency_neg σ c) z
  have hpositive (m : ℕ+) : H (ρ ((m:ℕ):ℤ)) = 0 := by
    change ((σ n:ℂ)-((hillBalancedGapFrequency σ c ((m:ℕ):ℤ))^2-(c:ℂ)))*
      (2*hillBalancedGapFrequency σ c ((m:ℕ):ℤ)*P ((hillBalancedGapFrequency σ c ((m:ℕ):ℤ))^2-(c:ℂ))) = 0
    rw [hillBalancedGapFrequency_pos_sq]
    by_cases hm : m = n
    · rw [hm,sub_self,zero_mul]
    · rw [hzeros m hm,mul_zero,mul_zero]
  have hroot (j : ℤ) : H (ρ j) = 0 := by
    rcases lt_trichotomy j 0 with hj | hj | hj
    · let m : ℕ+ := ⟨(-j).toNat,by omega⟩
      have hindex : -((m:ℕ):ℤ) = j := by
        change -(((-j).toNat:ℕ):ℤ) = j
        rw [Int.toNat_of_nonneg (by omega)]
        exact neg_neg j
      rw [← hindex]
      change H (hillBalancedGapFrequency σ c (-((m:ℕ):ℤ))) = 0
      rw [hillBalancedGapFrequency_neg,hHodd,hpositive m,neg_zero]
    · subst j
      dsimp only [H,ρ]
      rw [hillBalancedGapFrequency_zero]
      simp only [mul_zero,zero_mul]
    · let m : ℕ+ := ⟨j.toNat,by omega⟩
      have hindex : ((m:ℕ):ℤ) = j := by
        change ((j.toNat:ℕ):ℤ) = j
        exact Int.toNat_of_nonneg hj.le
      have h := hpositive m
      rw [hindex] at h
      exact h
  have hcommon (z : ℂ) (hz : G z = 0) : H z = 0 := by
    obtain ⟨j,hj⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp (by norm_num) ρ hρ z).mp hz
    rw [← hj]
    exact hroot j
  have hGne : G ≠ 0 := by
    have hzero : G 0 = 0 := by
      have h := entireSingleSpectralProduct_root (by norm_num) ρ hρ 0
      simpa only [ρ,hillBalancedGapFrequency_zero] using h
    have hd := hsimple 0 hzero
    intro he
    have hz : deriv G 0 = 0 := by rw [he]; simp
    exact hd hz
  apply exists_nonzero_const_factor_of_odd_simple_interpolation H G hH hG
    (quadratic_restoration_ne_zero P hP hPne (σ n:ℂ) (c:ℂ)) hGne hHodd hGodd hcommon hsimple
    centralCircleRadius tendsto_centralCircleRadius_atTop
  · obtain ⟨K,hK⟩ := eventually_centralCircle_entireSingleSpectralProduct_ne_zero (by norm_num) ρ hρ
    filter_upwards [eventually_ge_atTop K] with k hk
    exact hK k hk
  · exact restored_quadratic_product_quotient_subquadratic (by norm_num) ρ hρ P (σ n:ℂ) (c:ℂ) hsmall

end NLS.KdV
