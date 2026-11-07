import NLS.KdV.HillRealRestoredProduct
import NLS.KdV.HillEnergyProductCutoffs
import NLS.ComplexAnalysis.EntireConvergenceCancellation
import NLS.ComplexAnalysis.QuadraticConvergenceDescent

/-! The entire real-source Hill energy numerator is a NONZERO scalar
times its LITERAL retained-zero product, locally uniformly on the WHOLE
energy plane. Entire cancellation includes the omitted zero and the
quadratic ramification energy. The universal source normalization of
the scalar is a separate obligation. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_real_hill_energy_product_scalar
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (hPne : P ≠ 0) (n : ℕ+) (σ : ℕ+ → ℝ)
    (hσ : ∀ m : ℕ+, σ m ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))))
    (hzeros : ∀ m : ℕ+, m ≠ n → P (σ m:ℂ) = 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ z ∈ sphere (0:ℂ) (centralCircleRadius k), ‖(2*z*P (z^2-(c:ℂ)))/(-2*sin z)‖ ≤ ε) :
    ∃ A : ℂ, A ≠ 0 ∧
      TendstoLocallyUniformlyOn (fun N E => A*hillEnergyDeletedPartialProduct σ n E N) P atTop univ := by
  obtain ⟨C,hC,hfactor⟩ := exists_real_hill_restored_product_factor q hq u c hi hc P hP hPne n σ hσ hzeros hsmall
  let den : ℂ := ((Real.pi:ℂ)*(n:ℕ))^2
  have hden : den ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  let A : ℂ := -C/den
  have hA : A ≠ 0 := div_ne_zero (neg_ne_zero.mpr hC) hden
  let ρ := hillBalancedGapFrequency σ c
  let S : Set ℂ := {0,ρ ((n:ℕ):ℤ),-ρ ((n:ℕ):ℤ)}
  have hS : S.Countable :=
    (((Set.finite_singleton (-ρ ((n:ℕ):ℤ))).insert (ρ ((n:ℕ):ℤ))).insert 0).countable
  have hρ := memlp_hillBalancedGapFrequency_displacement q hq u c hi hc σ hσ
  have hlimit : ∀ z : ℂ, entireSingleSpectralProduct ρ z =
      hillEnergyRestoringPolynomial σ n c z*(P (z^2-(c:ℂ))/A) := by
    intro z
    apply mul_left_cancel₀ hC
    calc
      C*entireSingleSpectralProduct ρ z = ((σ n:ℂ)-(z^2-(c:ℂ)))*(2*z*P (z^2-(c:ℂ))) := (hfactor z).symm
      _ = C*(hillEnergyRestoringPolynomial σ n c z*(P (z^2-(c:ℂ))/A)) := by
        dsimp only [A,den,hillEnergyRestoringPolynomial]
        field_simp [hC,hden]
  have hfrequency : TendstoLocallyUniformlyOn
      (fun N z => hillEnergyDeletedPartialProduct σ n (z^2-(c:ℂ)) N)
      (fun z => P (z^2-(c:ℂ))/A) atTop univ := by
    apply tendstoLocallyUniformlyOn_cancel_entire_factor
      (fun N z => singleSpectralPartialProduct ρ z N)
      (fun N z => hillEnergyDeletedPartialProduct σ n (z^2-(c:ℂ)) N)
      (entireSingleSpectralProduct ρ) (fun z => P (z^2-(c:ℂ))/A)
      (hillEnergyRestoringPolynomial σ n c) _ _ _ S hS
      (hillEnergyRestoringPolynomial_ne_zero_off_finite σ n c) _ hlimit
      (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by norm_num) ρ hρ)
    · intro N z
      exact ((analyticOnNhd_hillEnergyDeletedPartialProduct σ n N _ (mem_univ _)).comp
        (f := fun w : ℂ => w^2-(c:ℂ)) ((analyticAt_id.pow 2).sub analyticAt_const)).differentiableAt
    · intro z _
      exact ((hP _ (mem_univ _)).comp (f := fun w : ℂ => w^2-(c:ℂ))
        ((analyticAt_id.pow 2).sub analyticAt_const)).div_const
    · change Continuous (fun z : ℂ => -2*z*(((σ n:ℂ)-(z^2-(c:ℂ)))/((Real.pi:ℂ)*(n:ℕ))^2))
      fun_prop
    · filter_upwards [eventually_ge_atTop (n:ℕ)] with N hN
      exact singleSpectralPartialProduct_balanced_deleted σ n c N hN
  have henergy : TendstoLocallyUniformlyOn (fun N E => hillEnergyDeletedPartialProduct σ n E N)
      (fun E => P E/A) atTop univ :=
    tendstoLocallyUniformlyOn_of_quadratic_pullback _ _ (c:ℂ) hfrequency
  have hscaled : TendstoLocallyUniformlyOn (fun N E => A*hillEnergyDeletedPartialProduct σ n E N)
      (fun E => A*(P E/A)) atTop univ :=
    (tendstoLocallyUniformlyOn_const_family (fun _ : ℂ => A) univ).mul₀ henergy continuousOn_const
      ((continuousOn_univ.mp hP.continuousOn).div_const A).continuousOn
  refine ⟨A,hA,hscaled.congr_right ?_⟩
  intro E _
  field_simp [hA]

end NLS.KdV
