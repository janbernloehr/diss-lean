import NLS.KdV.HillHminusPhysicalMomentIdentification
import NLS.KdV.HillHminusPhysicalMiuraFrequencySeries

/-! The actual original second-moment series converges absolutely near zero
and has a genuine analytic extension in the full complex H-minus-one topology.
Both the numerator and the entire contour, primitive and root normalization
are identified. No frequency identity or fixed-source summability is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- ONE complex rough ball supports analytic extensions of the ORIGINAL
physical second-moment corrections for ALL positive indices. The literal
natural-index series is absolutely convergent, including every closed gap. -/
theorem exists_hillOriginal_analytic_second_moment_series :
    ∃ δ : ℝ, ∃ F : ℕ+ → PeriodOneHminusOne → ℂ, 0<δ ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (F n) (ball (0 : PeriodOneHminusOne) δ)) ∧
      ∀ q : RealPeriodOneHillPotential, hillOriginalHminusSource q.val ∈ ball (0 : PeriodOneHminusOne) δ →
      ∀ n : ℕ+,
        Summable (fun k : ℕ => ‖(k : ℂ)*hillIntrinsicFrequencyMoment
          q.val q.property.1 q.property.2 n n.pos k 2‖) ∧
        F n (hillOriginalHminusSource q.val) =
          -12*∑' k : ℕ, (k : ℂ)*hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 := by
  obtain ⟨C,δ₀,W₀,W,s,hδ₀,_,_,hnum,_,hseries⟩ :=
    exists_hillHminus_physical_numerator_miura_frequency_series
  obtain ⟨δ₁,hδ₁,hmatch⟩ := exists_hillHminus_miura_moments_eq_original
  let δ := min δ₀ δ₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  have hsub₀ : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δ₀ := ball_subset_ball (min_le_left _ _)
  have hsub₁ : ball (0 : PeriodOneHminusOne) δ ⊆ ball 0 δ₁ := ball_subset_ball (min_le_right _ _)
  refine ⟨δ,hillHminusMiuraMomentFrequencyCorrection C s,hδ,?_,?_⟩
  · intro n
    exact (hseries n).2.1.mono hsub₀
  · intro q hq n
    have he (k : ℕ+) : hillHminusMiuraMoment C s n k 2 (hillOriginalHminusSource q.val) =
        hillIntrinsicFrequencyMoment q.val q.property.1 q.property.2 n n.pos k 2 :=
      hmatch C s q (hsub₁ hq) n (hnum q (hsub₀ hq) n) k 2
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
