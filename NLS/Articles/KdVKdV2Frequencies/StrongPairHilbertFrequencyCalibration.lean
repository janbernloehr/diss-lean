import NLS.Articles.KdVKdV2Frequencies.StrongLpFrequencyPairInvariance
import NLS.Articles.KdVKdV2Frequencies.RawActionHilbertInclusion
import NLS.Articles.KdVConvexity.IntrinsicPhysicalFrequencies

/-! The actual strong pair packet is calibrated with the SAME global
Hilbert physical frequency map on EVERY real raw-action fiber. Finite
pair truncation preserves literal actions and includes every zero mode. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem strong_pair_correction_eq_hilbert_frequency
    (V : Set ActionSpace) (G : ActionSpace → ActionSpace) (hcone : positiveQuadrant⊆V)
    (hG : AnalyticOnNhd ℂ G V)
    (hrec : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      G (originalActionInclusion b.val) n=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3)
    {D : GlobalRoughAbelianForwardData} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (P : StrongLpFrequencyPairChart D r) (z : Coeff 2 × Coeff 2) (hz : z∈P.domain)
    (hzr : z∈Coeff.realPairLocus 2) (n : ℕ+) :
    P.correction n z=G (rawActionHilbertInclusion (quadraticActionsExponent (q := 1) z)) n := by
  have ht := Coeff.tendsto_truncatePair (by norm_num : (2 : ℝ≥0∞)≠⊤) z
  have hleft := (P.analytic_correction n z hz).continuousAt.tendsto.comp ht
  have hqa : ContinuousAt (fun w : Coeff 2 × Coeff 2 => rawActionHilbertInclusion (quadraticActionsExponent (q := 1) w)) z :=
    rawActionHilbertInclusion.continuous.continuousAt.comp
      (analyticOnNhd_quadraticActionsExponent z (mem_univ _)).continuousAt
  have hpos := rawActionHilbertInclusion_nonnegative _ (Coeff.quadraticActions_mem_nonnegativeLocus z hzr)
  have hright := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 n).continuous.continuousAt.comp
    (f := fun w : Coeff 2 × Coeff 2 => G (rawActionHilbertInclusion (quadraticActionsExponent (q := 1) w)))
    ((hG _ (hcone hpos)).continuousAt.comp
      (f := fun w : Coeff 2 × Coeff 2 => rawActionHilbertInclusion (quadraticActionsExponent (q := 1) w)) hqa)).tendsto.comp ht
  have heq : (fun S => P.correction n (Coeff.truncatePair S z)) =ᶠ[atTop]
      (fun S => G (rawActionHilbertInclusion (quadraticActionsExponent (q := 1) (Coeff.truncatePair S z))) n) := by
    filter_upwards [ht (P.domain_open.mem_nhds hz)] with S hS
    obtain ⟨b,hb,hbf⟩ := P.finite_physical_recovery (Coeff.truncatePair S z) hS
      (Coeff.truncatePair_mem_realPairLocus S z hzr) S (by
        intro k hk
        simp only [Coeff.truncatePair,Coeff.truncate_apply,if_neg hk,and_self])
    have hJ := originalActionInclusion_eq_of_raw_coeffs b.val (quadraticActionsExponent (q := 1) (Coeff.truncatePair S z)) hb
    rw [hbf n,←hrec b n,hJ]
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

end NLS.Articles.KdVKdV2Frequencies
