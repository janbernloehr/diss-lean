import NLS.KdV.HillHminusChartPhysicalNumeratorBall
import NLS.KdV.HillHminusPhysicalMomentIdentification
import NLS.KdV.HillHminusOneSpectralMiuraFrequencySeries

/-! The SAME actual convergent original second-moment correction retains
isospectral invariance on its full real rough ball. This is the spectral
invariance needed for analytic descent through the original actions. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- One complex rough ball supports analytic ORIGINAL physical corrections
and the actual spectral invariance of THOSE SAME functions at all real rough
inputs. No invariant or moment-identification function is assumed. -/
theorem exists_hillOriginal_isospectral_analytic_second_moment_series :
    ∃ δ : ℝ, ∃ F : ℕ+ → PeriodOneHminusOne → ℂ, 0<δ ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (F n) (ball (0 : PeriodOneHminusOne) δ)) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
        IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p →
        hillHminusDiscriminant p=hillHminusDiscriminant q → ∀ n : ℕ+, F n p=F n q) ∧
      ∀ q : RealPeriodOneHillPotential, hillOriginalHminusSource q.val∈ball (0 : PeriodOneHminusOne) δ →
        ∀ n : ℕ+, Summable (fun k : ℕ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment
          q.val q.property.1 q.property.2 n n.pos k 2‖) ∧
        F n (hillOriginalHminusSource q.val) =
          -12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 := by
  obtain ⟨C,δ₀,W₀,W,s,hδ₀,hC,hpos,him,hr,H,_,_,_,_,_,hseries,hinv⟩ :=
    exists_hillHminus_analytic_spectral_miura_frequency_series
  have hreal : ∀ q∈C.domain, IsRealPeriodOneHminusOne q →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource q)) := fun q hq hqr =>
    hr q hq ((periodOneHminusConjugation_fixed_iff q).mpr hqr)
  obtain ⟨δ₁,hδ₁,_,hnum⟩ := C.exists_original_numerator_ball (hC (mem_ball_self hδ₀)) hpos him hreal H
  obtain ⟨δ₂,hδ₂,hmatch⟩ := exists_hillHminus_miura_moments_eq_original
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hsub₀ : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₀ := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₁ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub₂ : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ,hillHminusMiuraMomentFrequencyCorrection C s,hδ,?_,?_,?_⟩
  · intro n
    exact (hseries n).2.1.mono hsub₀
  · intro q hq p hp hqr hpr htrace n
    exact (hinv q (hsub₀ hq) p (hsub₀ hp)
      ((periodOneHminusConjugation_fixed_iff q).mpr hqr)
      ((periodOneHminusConjugation_fixed_iff p).mpr hpr) htrace n).2
  · intro q hq n
    have he (k : ℕ+) : hillHminusMiuraMoment C s n k 2 (hillOriginalHminusSource q.val)=
        hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 :=
      hmatch C s q (hsub₂ hq) n (hnum q (hsub₁ hq) n) k 2
    have hs : Summable (fun k : ℕ+ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment
        q.val q.property.1 q.property.2 n n.pos k 2‖) := by
      apply ((hseries n).1 _ (hsub₀ hq)).congr
      intro k
      rw [he k]
    refine ⟨summable_pnat_iff_summable_nat.mp hs,?_⟩
    unfold hillHminusMiuraMomentFrequencyCorrection
    congr 1
    calc
      _ = ∑' k : ℕ+, (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 :=
        tsum_congr (fun k => by rw [he k])
      _ = _ := tsum_pnat_eq_tsum_of_eq_zero
        (f := fun k : ℕ => (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2) (by simp)

end NLS.KdV
