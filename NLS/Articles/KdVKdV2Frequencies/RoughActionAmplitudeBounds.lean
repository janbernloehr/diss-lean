import NLS.Articles.KdVKdV2Frequencies.RoughUniformActionAmplitudes
import NLS.KdV.HillAbelianFourierSymbol

/-! # Uniform upper and positive lower bounds for actual rough action amplitudes

The native ell-infinity continuity and the actual free Fourier symbol give
one complex rough ball before every source and positive output mode.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

open NLS.KdV

theorem exists_hillHminus_native_action_amplitude_symbol_bounds :
    ∃ η C : ℝ, ∃ M : PeriodOneHminusOne → Coeff ⊤,
      0<η ∧ 0<C ∧ AnalyticOnNhd ℂ M (ball (0 : PeriodOneHminusOne) η) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ n : ℕ+,
        (1/8 : ℝ)≤‖M q (n : ℤ)‖ ∧ ‖M q (n : ℤ)‖≤C) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
          M (hillPhysicalHminusEmbedding p).val (n : ℤ)=
            (Real.sqrt (1+(n : ℝ)) : ℂ)*
              hillAbelianAmplitudePrefactor p.val p.property.1 p.property.2 (n : ℕ) := by
  obtain ⟨r,C,M,hr,hC,hMa,hb,hfree,hphys⟩ := exists_hillHminus_native_action_amplitude_symbol
  have hc := (hMa 0 (mem_ball_self hr)).continuousAt
  have hnear : ∀ᶠ q in 𝓝 (0 : PeriodOneHminusOne), ‖M q-M 0‖<(1/8 : ℝ) := by
    simpa only [mem_ball,dist_eq_norm] using
      hc.eventually (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ)<1/8)))
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hnear
  let η := min r δ
  have hη : 0<η := lt_min hr hδ
  have hsub : ball (0 : PeriodOneHminusOne) η⊆ball (0 : PeriodOneHminusOne) r :=
    ball_subset_ball (min_le_left _ _)
  have hM0 (n : ℕ+) : M 0 (n : ℤ)=hillAbelianFourierSymbol (n : ℤ) := by
    rw [hfree]
    change (Real.sqrt (1+(n : ℝ)) : ℂ)*(Real.sqrt (2*(n : ℝ)*Real.pi) : ℂ)⁻¹=
      if (n : ℤ)=0 then 0 else _
    rw [if_neg (by exact_mod_cast n.ne_zero)]
    simp only [Int.natAbs_natCast,div_eq_mul_inv]
  refine ⟨η,C,M,hη,hC,hMa.mono hsub,?_,fun p hp n => hphys p (hsub hp) n⟩
  intro q hq n
  refine ⟨?_,(lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞)≠0) (M q) _).trans (hb q (hsub hq)).1⟩
  have hsmall : ‖M q-M 0‖<(1/8 : ℝ) := hd
    (by simpa only [mem_ball] using (ball_subset_ball (min_le_right r δ) hq))
  have hcoord : ‖M q (n : ℤ)-M 0 (n : ℤ)‖≤‖M q-M 0‖ :=
    lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞)≠0) (M q-M 0) (n : ℤ)
  have hl : (1/4 : ℝ)≤‖M 0 (n : ℤ)‖ := by
    rw [hM0]
    exact hillAbelianFourierSymbol_lower _ (by exact_mod_cast n.ne_zero)
  have htriangle : ‖M 0 (n : ℤ)‖≤‖M q (n : ℤ)-M 0 (n : ℤ)‖+‖M q (n : ℤ)‖ := by
    calc
      _ = ‖(M 0 (n : ℤ)-M q (n : ℤ))+M q (n : ℤ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖M 0 (n : ℤ)-M q (n : ℤ)‖+‖M q (n : ℤ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  linarith

end NLS.Articles.KdVKdV2Frequencies
