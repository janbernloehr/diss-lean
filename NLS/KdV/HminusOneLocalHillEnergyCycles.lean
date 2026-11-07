import NLS.KdV.HminusOneLocalHillDifferential
import NLS.KdV.HillHminusOneMiuraAllLabels
import NLS.ComplexAnalysis.QuadraticEnergyCircleWinding

/-! Actual local Hill cycles wind once around BOTH original periodic
endpoints, including collapsed gaps, and normalize ALL positive-index
differentials on a common source and energy domain. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusDirichletBall

theorem energyCircle_winding_original_endpoints (B : HillHminusDirichletBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) :
    let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      (B.miuraBall.actionBall.shift:ℂ)
    Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) = 1 ∧
      Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)):ℂ) = 1 := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,
    B.miuraBall.actionBall.lift_real q hq hr⟩
  have he := hillHminusLabels_pair_eq_squared_miuraDirac q hr u B.miuraBall.actionBall.shift
    (B.miuraBall.actionBall.image q hq) (B.miuraBall.actionBall.outside q hq) (m:ℕ) m.pos
  have him := hillMiuraDiracPair_real u ((m:ℕ):ℤ)
  have hl : ((hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re:ℂ) = hillMiuraDiracLeft u.val ((m:ℕ):ℤ) :=
    Complex.ext rfl him.1.symm
  have hh : ((hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re:ℂ) = hillMiuraDiracRight u.val ((m:ℕ):ℤ) :=
    Complex.ext rfl him.2.symm
  dsimp only
  constructor
  · rw [he.1,Complex.ofReal_sub,Complex.ofReal_pow,hl]
    exact windingIntegral_quadraticEnergyCircle_one_of_positive D.center D.radius _ _ hpos
      (D.gap (left_mem_segment ℝ _ _))
  · rw [he.2,Complex.ofReal_sub,Complex.ofReal_pow,hh]
    exact windingIntegral_quadraticEnergyCircle_one_of_positive D.center D.radius _ _ hpos
      (D.gap (right_mem_segment ℝ _ _))

/-- The same actual cycle is chosen before all differential indices. -/
theorem exists_normalized_energyCircle (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ),
      0 < D.center-D.radius ∧
      let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
        (B.miuraBall.actionBall.shift:ℂ)
      Γ.Inside {E | (E,q) ∈ B.energyDomain A} ∧
      Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) = 1 ∧
      Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)):ℂ) = 1 ∧
      ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral
        (fun E => B.energyDifferential A n (E,q)) = if m = n then 1 else 0 := by
  let u : PeriodOneRealL2 := ⟨B.miuraBall.actionBall.lift q,
    B.miuraBall.actionBall.lift_real q hq.1 hr⟩
  obtain ⟨D,hD,_,_,_⟩ := A.exists_positive_energyCircle u (B.miuraBall.actionBall.shift:ℂ) m
  have hw := B.energyCircle_winding_original_endpoints q hq.1 hr m D hD
  exact ⟨D,hD,B.energyCircle_inside A q hq m D hD,hw.1,hw.2,
    fun n => B.energyDifferential_circle_period A q hq n m D hD⟩

end HillHminusDirichletBall
end NLS.KdV
