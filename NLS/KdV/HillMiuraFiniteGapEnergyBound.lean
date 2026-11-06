import NLS.KdV.HillMiuraGroundEnergy
import NLS.ZakharovShabat.SourceZeroGapMassEstimate

/-! # The actual normalized finite-gap Miura energy bound

The bound applies to every real mean-zero L2 factor with finitely many
actual open Dirac gaps. It retains the original first weighted actions;
identification with the global weak Hill target is a separate obligation.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillMiura_finiteGap_norm_sq_le_weak_weighted_actions
    (u : PeriodOneRealL2) (hm : u.val 0 = 0)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖u.val‖^2 ≤ ∑ n ∈ hf.toFinset,
      sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) := by
  obtain ⟨hl,hr⟩ := hillMiura_central_endpoints_eq_zero u hm
  have h := sourceFiniteGap_half_norm_sq_le_weak_weighted_actions (hillMiuraRealSource u) hf hl hr
  have hn := WithLp.prod_norm_sq_eq_of_L2 (hillMiuraDiagonal u.val)
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd] at hn
  change ‖hillMiuraDiagonal u.val‖^2/2 ≤ _ at h
  linarith

theorem miura_finiteGap_ground_energy_le_weak_weighted_actions
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hn : ‖u.val‖^2 = e)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    -hillHminusLowestRealRoot q hr ≤
      ∑ n ∈ hf.toFinset, sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) := by
  rw [←neg_miura_energy_eq_hillHminusLowestRealRoot q hr u e hm hi,neg_neg,←hn]
  exact hillMiura_finiteGap_norm_sq_le_weak_weighted_actions u hm hf

end NLS.KdV
