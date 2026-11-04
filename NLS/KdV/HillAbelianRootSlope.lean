import NLS.KdV.HillAbelianRootUpdate
import NLS.KdV.HillAbelianPeriodConjugation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem multipliable_hillAbelian_factor_omission (n m : ℕ) (E : ℂ) (a : Coeff 2) :
    Multipliable (fun j : ℕ => if j+1 = m then 1 else hillAbelianComplexNumeratorFactor n (E,a) j) := by
  have hs : Summable (fun j : ℕ => ‖(if j+1 = m then 1 else hillAbelianComplexNumeratorFactor n (E,a) j)-1‖) := by
    apply (summable_norm_hillAbelianComplexNumeratorFactor_sub_one n (E,a)).of_nonneg_of_le
      (fun j => norm_nonneg _)
    intro j
    split_ifs
    · simp only [sub_self,norm_zero]
      exact norm_nonneg _
    · exact le_rfl
  have hp := multipliable_one_add_of_summable hs
  simpa only [add_sub_cancel] using hp

theorem hillAbelianHilbertPsi_rootUpdate_factorization
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (E : ℂ) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s)) =
      (s-E)*(2/((n:ℂ)*Real.pi)/(freeHillValue m:ℂ))*
        ∏' j : ℕ, if j+1 = m then 1 else hillAbelianComplexNumeratorFactor n (E,a) j := by
  let f := hillAbelianComplexNumeratorFactor n (E,hillAbelianRootUpdate m (a,s))
  let g : ℕ → ℂ := fun j => if j+1 = m then 1 else hillAbelianComplexNumeratorFactor n (E,a) j
  have hsame : f (m-1) = (s-E)/(freeHillValue m:ℂ) := by
    dsimp only [f,hillAbelianComplexNumeratorFactor]
    rw [Nat.sub_add_cancel hm,if_neg hmn]
    change (hillAbelianHilbertRootEnergy (hillAbelianRootUpdate m (a,s)) m-E)/(freeHillValue m:ℂ) = _
    rw [hillAbelianHilbertRootEnergy_update_same m hm a s]
  have hother (j : ℕ) (hj : j ≠ m-1) : f j = hillAbelianComplexNumeratorFactor n (E,a) j := by
    have hcast : ((j+1:ℕ):ℤ) ≠ (m:ℤ) := by exact_mod_cast (show j+1 ≠ m by omega)
    dsimp only [f,hillAbelianComplexNumeratorFactor]
    split_ifs
    · rfl
    · rw [hillAbelianRootUpdate_apply_other m a s _ hcast]
  have hcut (j : ℕ) : (if j = m-1 then 1 else f j) = g j := by
    by_cases hj : j = m-1
    · subst j
      simp only [g,Nat.sub_add_cancel hm,ite_true]
    · have hjm : j+1 ≠ m := by omega
      simp only [if_neg hj,g,if_neg hjm,hother j hj]
  have hup : Function.update f (m-1) 1 = g := by
    funext j
    rw [Function.update_apply]
    exact hcut j
  have hmulti : Multipliable (Function.update f (m-1) 1) := by
    rw [hup]
    exact multipliable_hillAbelian_factor_omission n m E a
  have hp := Multipliable.tprod_eq_mul_tprod_ite' (f := f) (m-1) hmulti
  simp_rw [hcut] at hp
  rw [hillAbelianHilbertPsi,hillAbelianHilbertProduct_eq_tprod]
  change (2/((n:ℂ)*Real.pi))*(∏' j, f j) = _
  rw [hp,hsame]
  dsimp only [g]
  ring

def hillAbelianRootSlope (n m : ℕ) (E : ℂ) (a : Coeff 2) : ℂ :=
  hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,E+1))

theorem hillAbelianHilbertPsi_rootUpdate_eq_rootSlope
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (E : ℂ) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s)) =
      (s-E)*hillAbelianRootSlope n m E a := by
  rw [hillAbelianRootSlope,hillAbelianHilbertPsi_rootUpdate_factorization n m hm hmn E a s,
    hillAbelianHilbertPsi_rootUpdate_factorization n m hm hmn E a (E+1)]
  ring

theorem analyticOnNhd_hillAbelianRootSlope (n m : ℕ) (a : Coeff 2) :
    AnalyticOnNhd ℂ (fun E => hillAbelianRootSlope n m E a) univ := by
  intro E _
  have hu := (analyticOnNhd_hillAbelianRootUpdate m (a,E+1) (mem_univ _)).comp
    (f := fun E : ℂ => (a,E+1)) (analyticAt_const.prod (analyticAt_id.add analyticAt_const))
  exact (analyticOnNhd_hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,E+1)) (mem_univ _)).comp
    (f := fun E : ℂ => (E,hillAbelianRootUpdate m (a,E+1))) (analyticAt_id.prod hu)

theorem hillAbelianRootSlope_conj (n m : ℕ) (E : ℂ) (a : Coeff 2) :
    hillAbelianRootSlope n m (conj E) (star a) = conj (hillAbelianRootSlope n m E a) := by
  unfold hillAbelianRootSlope
  rw [show conj E+1 = conj (E+1) by simp, hillAbelianRootUpdate_star]
  exact hillAbelianHilbertPsi_conj n E _

theorem hillAbelianRootSlope_im_eq_zero (n m : ℕ) (a : Coeff 2) (ha : star a = a) (x : ℝ) :
    (hillAbelianRootSlope n m (x:ℂ) a).im = 0 := by
  have hc := hillAbelianRootSlope_conj n m (x:ℂ) a
  rw [conj_ofReal,ha] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

end NLS.KdV
