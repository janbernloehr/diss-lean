import NLS.KdV.HminusOneCanonicalHillPsi
import NLS.KdV.HminusOneLocalHillEnergyCycles

/-! The intrinsic numerator retains the ACTUAL normalized periods in
every local presentation. All complex sources in a ball admit actual
frequency circles. At real sources the genuine energy cycles are chosen
before ALL numerator indices and wind once around BOTH original labels,
including repeated endpoints. Energy roots remain local presentations. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace HillHminusPsiBall

theorem canonical_differential_eq (B : HillHminusPsiBall) (n : ℕ+) (E : ℂ)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusCanonicalPsi n (E,q)/B.parent.energyRoot (E,q) =
      B.parent.energyDifferential B.family n (E,q) := by
  rw [B.canonical_numerator_eq n E q hq]
  rfl

theorem nonempty_canonicalPeriodCircle (B : HillHminusPsiBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (m : ℕ+) :
    Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :=
  B.parent.nonempty_psiPeriodCircle B.family q (B.subset hq) m

theorem canonical_pullback_period (B : HillHminusPsiBall) (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ)) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
      (2*z*hillHminusCanonicalPsi n (z^2-(B.parent.miuraBall.actionBall.shift:ℂ),q))/
        sourceCanonicalRoot (by norm_num) (by norm_num)
          (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) z) = if m = n then 1 else 0 := by
  simp_rw [B.canonical_numerator_eq n _ q hq]
  exact B.parent.psiNumerator_pullback_period B.family n m q (B.subset hq) D

/-- One actual energy cycle normalizes ALL intrinsic numerators. -/
theorem exists_canonical_normalized_energyCircle (B : HillHminusPsiBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift q)) ((m:ℕ):ℤ),
      0 < D.center-D.radius ∧
      let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
        (B.parent.miuraBall.actionBall.shift:ℂ)
      Γ.Inside {E | (E,q) ∈ B.parent.energyDomain B.family} ∧
      Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)-1):ℂ) = 1 ∧
      Γ.windingIntegral (hillHminusLabels q hr (2*(m:ℕ)):ℂ) = 1 ∧
      ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral
        (fun E => hillHminusCanonicalPsi n (E,q)/B.parent.energyRoot (E,q)) = if m = n then 1 else 0 := by
  obtain ⟨D,hD,hin,hl,hr',hper⟩ := B.parent.exists_normalized_energyCircle B.family q (B.subset hq) hr m
  refine ⟨D,hD,hin,hl,hr',?_⟩
  intro n
  simp_rw [B.canonical_differential_eq n _ q hq]
  exact hper n

end HillHminusPsiBall
end NLS.KdV
