import NLS.KdV.HillFullAbelianPhase
import NLS.MKdV.MiuraFiniteGapAbelianPhase

/-! # The full independent Abelian unit phase on the original real H¹ domain

All original physical-action supports and signed means are allowed.
Only continuity on the phase's own open-action domain is asserted;
its negative physical Gardner generators remain a separate obligation.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraFullAbelianPhase (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) : ℂ :=
  hillFullAbelianPhase (realSobolevMiuraHillPotential a ha) n hn

theorem miuraFullAbelian_corrections_summable (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => hillDirichletRegularAbelianTerm (realSobolevMiuraHillPotential a ha)
      n hn (k+1) (by omega)) := summable_hillDirichletRegularAbelianTerm _ n hn

theorem norm_miuraFullAbelianPhase (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n ≠ 0) : ‖miuraFullAbelianPhase a ha n hn‖ = 1 :=
  norm_hillFullAbelianPhase _ n hn
    (fun h => hJ ((realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha n hn).mp h))

theorem miuraFullAbelianPhase_closed (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hJ : miuraMKdVAction a ha n = 0) : miuraFullAbelianPhase a ha n hn = 0 :=
  hillFullAbelianPhase_closed _ n hn
    ((realSobolevMiuraHill_halfLength_zero_iff_action_zero a ha n hn).mpr hJ)

theorem norm_miuraFullAbelianPhase_le_one (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ‖miuraFullAbelianPhase a ha n hn‖ ≤ 1 := norm_hillFullAbelianPhase_le_one _ n hn

theorem continuousAt_miuraFullAbelianPhase_along_real_family
    {T : Type*} [TopologicalSpace T] (A : T → ScalarDomain 2) (hA : Continuous A)
    (hreal : ∀ t j, (A t).val j = conj ((A t).val (-j)))
    (n : ℕ) (hn : 1 ≤ n) (t0 : T) (hJ : miuraMKdVAction (A t0) (hreal t0) n ≠ 0) :
    ContinuousAt (fun t => miuraFullAbelianPhase (A t) (hreal t) n hn) t0 := by
  have hgap : hillRealGapHalfLength (realSobolevMiuraHillPotential (A t0) (hreal t0)).val
      (realSobolevMiuraHillPotential (A t0) (hreal t0)).property.1
      (realSobolevMiuraHillPotential (A t0) (hreal t0)).property.2 n ≠ 0 :=
    fun h => hJ ((realSobolevMiuraHill_halfLength_zero_iff_action_zero (A t0) (hreal t0) n hn).mp h)
  exact (continuousAt_hillFullAbelianPhase _ n hn hgap).comp
    (f := fun t => realSobolevMiuraHillPotential (A t) (hreal t)) (x := t0)
    (continuous_realSobolevMiuraHillPotential_family A hA hreal).continuousAt

theorem continuousOn_miuraFullAbelianPhase_original_H1 (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun a : {a : ScalarDomain 2 // ∀ j, a.val j = conj (a.val (-j))} =>
      miuraFullAbelianPhase a.val a.property n hn) {a | miuraMKdVAction a.val a.property n ≠ 0} := by
  intro a ha
  exact (continuousAt_miuraFullAbelianPhase_along_real_family
    (fun b : {b : ScalarDomain 2 // ∀ j, b.val j = conj (b.val (-j))} => b.val)
    continuous_subtype_val (fun b => b.property) n hn a ha).continuousWithinAt

theorem miuraFullAbelianPhase_eq_finiteGap (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (hfg : miuraFiniteGap a ha) (n : ℕ) (hn : 1 ≤ n) :
    miuraFullAbelianPhase a ha n hn = miuraFiniteGapAbelianPhase a ha hfg n hn :=
  hillFullAbelianPhase_eq_finite_of_closed_complement _ n hn _
    (miuraFiniteGapAbelianSupport_closed_complement a ha hfg)

end NLS.MKdV
