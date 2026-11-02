import NLS.MKdV.MiuraAngleActionFlow
import NLS.MKdV.MiuraActionFlowUniqueness
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Independent physical action directions on the exact open-action stratum

The original restricted spectral angle differentials are biorthogonal
to the actual physical Gardner action vectors. They prove independence
on every open-action stratum, with arbitrary other gaps allowed to close.
The vector vanishes exactly when the physical action closes.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem linearIndependent_miuraGardnerDirections (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    LinearIndependent ℂ
      (fun n : {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0} =>
        l2GardnerDirection (miuraL2Action n.val) (scalarInclusion a)) := by
  classical
  rw [linearIndependent_iff']
  intro S c hc n hn
  have he := congrArg (miuraThetaDifferential n.val (scalarInclusion a)) hc
  have hk (k : {k : ℕ // 1 ≤ k ∧ miuraMKdVAction a ha k ≠ 0}) :
      miuraThetaDifferential n.val (scalarInclusion a)
        (l2GardnerDirection (miuraL2Action k.val) (scalarInclusion a)) =
        if k = n then 1 else 0 := by
    change miuraThetaGardnerBracket n.val k.val (scalarInclusion a) = _
    rw [miuraThetaGardnerBracket_of_action_ne_zero a ha n.val k.val n.property.1 k.property.1 n.property.2]
    by_cases hkn : k = n
    · subst k
      simp only [ite_true]
    · have hval : n.val ≠ k.val := fun h => hkn (Subtype.ext h.symm)
      simp only [hval,hkn,ite_false]
  simp only [map_sum,map_smul,map_zero,smul_eq_mul,hk] at he
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',if_pos hn] using he

theorem miuraGardnerDirection_eq_zero_of_action_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n)
    (hzero : miuraMKdVAction a ha n = 0) :
    l2GardnerDirection (miuraL2Action n) (scalarInclusion a) = 0 := by
  have he : (fun t => scalarInclusion (miuraH1ActionFlow a ha n t)) =
      (fun _ : ℝ => scalarInclusion a) := by
    funext t
    rw [miuraH1ActionFlow_eq_self_of_action_zero a ha n hn hzero t]
  have hd := hasDerivAt_miuraH1ActionFlow_Gardner a ha n hn 0
  rw [he,miuraH1ActionFlow_zero] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) (scalarInclusion a))

theorem miuraGardnerDirection_eq_zero_iff (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    l2GardnerDirection (miuraL2Action n) (scalarInclusion a) = 0 ↔
      miuraMKdVAction a ha n = 0 := by
  constructor
  · intro hz
    by_contra haction
    have he := miuraThetaGardnerBracket_of_action_ne_zero a ha n n hn hn haction
    simp only [miuraThetaGardnerBracket,hz,map_zero,ite_true] at he
    exact zero_ne_one he
  · exact miuraGardnerDirection_eq_zero_of_action_zero a ha n hn

end NLS.MKdV
