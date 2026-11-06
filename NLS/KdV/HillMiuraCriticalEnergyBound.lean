import NLS.KdV.HillMiuraCriticalActions
import NLS.KdV.HillMiuraSignedActions
import NLS.KdV.HillMiuraFiniteGapEnergyBound
import NLS.SequenceSpaces.SignedFiniteSum

/-! # The finite-gap critical energy bound in the original Hill actions

The two signed Dirac contributions combine into one positive Hill action.
The action normalization and the factor pi*n are retained literally.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillMiura_finiteGap_norm_sq_le_positive_weighted_actions
    (u : PeriodOneRealL2) (hm : u.val 0 = 0)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖u.val‖^2 ≤ 2*∑ n ∈ hf.toFinset.filter (fun n => 0 < n),
      sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) := by
  have hz : (0 : ℤ) ∉ hf.toFinset := by
    intro h
    have hgap := (Set.Finite.mem_toFinset hf).mp h
    change canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 ≠ 0 at hgap
    apply hgap
    rw [canonicalPeriodicGap,(hillMiura_central_endpoints_eq_zero u hm).1,
      (hillMiura_central_endpoints_eq_zero u hm).2,sub_self]
  have hs (n : ℤ) : -n ∈ hf.toFinset ↔ n ∈ hf.toFinset := by
    rw [Set.Finite.mem_toFinset hf,Set.Finite.mem_toFinset hf]
    change hillMiuraDiracRight u.val (-n)-hillMiuraDiracLeft u.val (-n) ≠ 0 ↔
      hillMiuraDiracRight u.val n-hillMiuraDiracLeft u.val n ≠ 0
    rw [(hillMiuraDiracPair_neg u.val).1 n,(hillMiuraDiracPair_neg u.val).2 n]
    ring_nf
  have hsum := sum_symmetric_int_eq_twice_positive hf.toFinset hz hs
    (fun n => sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ))) (by
      intro n
      rw [sourceRealHigherAction_miura_neg_one,Int.cast_neg]
      ring)
  rw [←hsum]
  exact hillMiura_finiteGap_norm_sq_le_weak_weighted_actions u hm hf

/-- An actual normalized finite-gap factor has energy bounded by a finite
sum of the original positive Hill actions, with coefficient one. -/
theorem hillMiura_critical_norm_sq_le_Hill_actions
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ s : Finset ℕ+, ‖u.val‖^2 ≤ ∑ n ∈ s,
      (hillHminusRealGapContourMoment q hr n 0).re/(Real.pi*(n : ℝ)) := by
  let t := hf.toFinset.filter (fun n => 0 < n)
  let p : ℤ → ℕ+ := fun n => n.toNat.toPNat'
  have hc (n : ℤ) (hn : n ∈ t) : ((p n : ℕ) : ℤ) = n := by
    have hnpos := (Finset.mem_filter.mp hn).2
    dsimp only [p]
    rw [PNat.toPNat'_coe (by omega : 0 < n.toNat)]
    omega
  have hinj : Set.InjOn p (t : Set ℤ) := by
    intro a ha b hb he
    have h := congrArg (fun n : ℕ+ => ((n : ℕ) : ℤ)) he
    rwa [hc a ha,hc b hb] at h
  refine ⟨t.image p,?_⟩
  have he : (∑ n ∈ t.image p, (hillHminusRealGapContourMoment q hr n 0).re/(Real.pi*(n : ℝ))) =
      2*∑ n ∈ t, sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) := by
    rw [Finset.sum_image hinj,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hillHminusRealGapContourMoment_eq_twice_critical_Dirac_action q hr u e hm hi (p n),ofReal_re]
    have hcast : (p n : ℝ) = (n : ℝ) := by exact_mod_cast hc n hn
    rw [hc n hn,hcast]
    ring
  rw [he]
  exact hillMiura_finiteGap_norm_sq_le_positive_weighted_actions u hm hf

/-- The same physical Hill-action bound at the intrinsic lowest energy. -/
theorem hillMiura_critical_ground_energy_le_Hill_actions
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hn : ‖u.val‖^2 = e)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ s : Finset ℕ+, -hillHminusLowestRealRoot q hr ≤ ∑ n ∈ s,
      (hillHminusRealGapContourMoment q hr n 0).re/(Real.pi*(n : ℝ)) := by
  obtain ⟨s,hs⟩ := hillMiura_critical_norm_sq_le_Hill_actions q hr u e hm hi hf
  refine ⟨s,?_⟩
  rw [←neg_miura_energy_eq_hillHminusLowestRealRoot q hr u e hm hi,neg_neg,←hn]
  exact hs

end NLS.KdV
