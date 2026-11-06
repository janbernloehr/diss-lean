import NLS.KdV.HillProductPeriodUniformLimit
import NLS.KdV.HillComplexPeriodDomainAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem exists_hillAbelianProductComplexPeriods_common_finite_neighborhood (N : ℕ) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      ∀ n k : ℕ, 1 ≤ k → k < N →
        AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr n k) (univ ×ˢ U) := by
  have hex (j : Fin N) : ∃ U : Set (Coeff 2), IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧
      (1 ≤ j.val → ∀ p ∈ U, ∀ E ∈ sphere (hillRealGapCenter q hq hr j.val : ℂ)
        (hillRealGapHalfLength q hq hr j.val+hillRealGapCollar q hq hr j.val),
        (E,p) ∈ hillAbelianComplexRootDomain q hq hr) := by
    by_cases hj : 1 ≤ j.val
    · obtain ⟨U,hU,hqU,hcircle⟩ := exists_hillAbelianComplexRoot_contour_neighborhood q hq hr j.val hj
      exact ⟨U,hU,hqU,fun _ => hcircle⟩
    · exact ⟨univ,isOpen_univ,mem_univ _,fun h => (hj h).elim⟩
  choose U hopen hmem hcircle using hex
  let V : Set (Coeff 2) := ⋂ j : Fin N, U j
  have hV : IsOpen V := isOpen_iInter_of_finite hopen
  have hqV : SpectralWeight.one.toCoeff q ∈ V := mem_iInter.mpr hmem
  refine ⟨V,hV,hqV,?_⟩
  intro n k hk hkN
  apply analyticOnNhd_hillAbelianProductComplexPeriod_of_domain q hq hr n k hk V hV
  intro p hp E hE
  exact hcircle ⟨k,hkN⟩ hk p ((mem_iInter.mp hp) ⟨k,hkN⟩) E hE

def hillFullLowComplexPeriodSequence (N : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 :=
  ∑ k ∈ Finset.range N, if 1 ≤ k then
    lp.single 2 (k : ℤ) ((-2*(Real.pi : ℂ))*
      hillAbelianProductComplexPeriod q hq hr 0 k t) else 0

theorem analyticOnNhd_hillFullLowComplexPeriodSequence
    (N : ℕ) (U : Set (Coeff 2))
    (hperiods : ∀ k : ℕ, 1 ≤ k → k < N →
      AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr 0 k) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillFullLowComplexPeriodSequence q hq hr N) (univ ×ˢ U) := by
  intro t ht
  unfold hillFullLowComplexPeriodSequence
  apply Finset.analyticAt_fun_sum
  intro k hk
  by_cases hkn : 1 ≤ k
  · simp only [if_pos hkn]
    have hA : AnalyticAt ℂ (fun v : Coeff 2 × Coeff 2 =>
        (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k v) t :=
      analyticAt_const.mul (hperiods k hkn (Finset.mem_range.mp hk) t ht)
    exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).analyticAt _).comp hA
  · simp only [if_neg hkn]
    exact analyticAt_const

theorem hillFullLowComplexPeriodSequence_apply_nat
    (N k : ℕ) (hk : 1 ≤ k) (t : Coeff 2 × Coeff 2) :
    hillFullLowComplexPeriodSequence q hq hr N t (k : ℤ) =
      if k < N then (-2*(Real.pi : ℂ))*hillAbelianProductComplexPeriod q hq hr 0 k t else 0 := by
  classical
  unfold hillFullLowComplexPeriodSequence
  simp only [lp.coeFn_sum,Finset.sum_apply]
  by_cases hkN : k < N
  · rw [Finset.sum_eq_single k,if_pos hk,if_pos hkN]
    · simp only [lp.single_apply,Pi.single_eq_same]
    · intro j _ hjk
      split_ifs
      · exact lp.single_apply_ne _ _ _ (by exact_mod_cast (Ne.symm hjk))
      · rfl
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hkN)).elim
  · rw [if_neg hkN]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : (k : ℤ) ≠ (j : ℤ) := by
      have hjN := Finset.mem_range.mp hj
      omega
    split_ifs
    · exact lp.single_apply_ne _ _ _ hjk
    · rfl

theorem hillFullLowComplexPeriodSequence_apply_nonpositive
    (N : ℕ) (t : Coeff 2 × Coeff 2) (m : ℤ) (hm : m ≤ 0) :
    hillFullLowComplexPeriodSequence q hq hr N t m = 0 := by
  classical
  unfold hillFullLowComplexPeriodSequence
  simp only [lp.coeFn_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkn : 1 ≤ k
  · rw [if_pos hkn]
    exact lp.single_apply_ne _ _ _ (by omega)
  · rw [if_neg hkn]
    rfl

end NLS.KdV
