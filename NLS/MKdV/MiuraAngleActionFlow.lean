import NLS.MKdV.MiuraActionFlowInvariants
import NLS.MKdV.MiuraAngleActionBracket
import NLS.ZakharovShabat.SourcePairedActionAngleFlow

/-! # The actual restricted spectral angle on the complete Gardner orbit

For an open selected physical action, the original single-valued NLS
phase has the exact global rotation law along every complete Gardner
action flow. All unselected angles stay fixed. The factor two is the
existing phase convention exp(2 i theta), not a changed angle speed.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraNLSGap_ne_zero_of_action_ne_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (hangle : miuraMKdVAction a ha m ≠ 0) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) (periodOnePotential_mem _) m ≠ 0 := by
  intro hg
  change miuraNLSRight a m-miuraNLSLeft a m = 0 at hg
  have hi := (miuraNLSAction_zero_iff_endpoints a ha m).mpr (sub_eq_zero.mp hg).symm
  exact hangle ((miuraMKdVAction_nonnegative_and_zero_iff a ha m hm).2.2.mpr hi)

theorem miuraThetaPhase_ne_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (hangle : miuraMKdVAction a ha m ≠ 0) : miuraThetaPhase m (scalarInclusion a) ≠ 0 := by
  rw [miuraThetaPhase,scalarL2Diagonal_scalarInclusion]
  exact miuraNLSAngleFamily.data.theta_phase_ne_zero _
    (miuraNLSAngleFamily.data.real_subset (realDiagonalH1Source a ha).property) m
    (miuraNLSGap_ne_zero_of_action_ne_zero a ha m hm hangle)

theorem norm_miuraThetaPhase (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m)
    (hangle : miuraMKdVAction a ha m ≠ 0) : ‖miuraThetaPhase m (scalarInclusion a)‖ = 1 := by
  rw [miuraThetaPhase,scalarL2Diagonal_scalarInclusion]
  exact miuraNLSAngleFamily.data.theta_phase_norm_real _
    (miuraNLSAngleFamily.data.real_subset (realDiagonalH1Source a ha).property)
    (realDiagonalH1Source a ha).property m
    (miuraNLSGap_ne_zero_of_action_ne_zero a ha m hm hangle)

theorem miuraThetaPhase_miuraActionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : miuraMKdVAction a ha m ≠ 0) (t : ℝ) :
    miuraThetaPhase m (scalarInclusion (miuraH1ActionFlow a ha n t)) =
      if m = n then Complex.exp (2*I*(t : ℂ))*miuraThetaPhase m (scalarInclusion a)
      else miuraThetaPhase m (scalarInclusion a) := by
  have he := miuraNLSAngleFamily.data.phase_pairedActionFlow miuraActionFlowFamily.data
    (realDiagonalH1Source a ha) m n (-(n : ℤ))
    (miuraNLSGap_ne_zero_of_action_ne_zero a ha m hm hangle) t
  have hs := congrArg Subtype.val (miuraH1ActionFlow_source a ha n t)
  change sobolevSourceInclusion (miuraH1ActionFlow a ha n t,miuraH1ActionFlow a ha n t) = _ at hs
  simp only [miuraThetaPhase,scalarL2Diagonal_scalarInclusion,hs]
  have hneg : (m : ℤ) ≠ -(n : ℤ) := by omega
  by_cases hmn : m = n
  · subst n
    simpa only [ite_true,hneg,ite_false,sub_zero,mul_one,realDiagonalH1Source] using! he
  · have hint : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast hmn
    simpa only [hmn,hint,hneg,ite_false,sub_self,mul_zero,zero_mul,Complex.exp_zero,one_mul,
      realDiagonalH1Source] using! he

theorem hasDerivAt_miuraThetaPhase_actionFlow (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : miuraMKdVAction a ha m ≠ 0) (t : ℝ) :
    HasDerivAt (fun u => miuraThetaPhase m (scalarInclusion (miuraH1ActionFlow a ha n u)))
      ((2*I*(if m = n then 1 else 0 : ℂ))*
        miuraThetaPhase m (scalarInclusion (miuraH1ActionFlow a ha n t))) t := by
  have he : (fun u => miuraThetaPhase m (scalarInclusion (miuraH1ActionFlow a ha n u))) =
      (fun u : ℝ => if m = n then Complex.exp (2*I*(u : ℂ))*miuraThetaPhase m (scalarInclusion a)
        else miuraThetaPhase m (scalarInclusion a)) := by
    funext u
    exact miuraThetaPhase_miuraActionFlow a ha m n hm hn hangle u
  rw [he]
  rw [miuraThetaPhase_miuraActionFlow a ha m n hm hn hangle t]
  by_cases hmn : m = n
  · subst n
    simp only [ite_true,mul_one]
    simpa only [mul_assoc] using
      (NLS.FunctionalAnalysis.hasDerivAt_scalarExponential (2*I) t).mul_const (miuraThetaPhase m (scalarInclusion a))
  · simp only [hmn,ite_false,mul_zero,zero_mul]
    exact hasDerivAt_const t _

end NLS.MKdV
