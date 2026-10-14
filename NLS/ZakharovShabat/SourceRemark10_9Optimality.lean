import NLS.ZakharovShabat.SourceMidpointQuotientSharpness

/-!
# The full p/2 optimality assertion in Remark 10.9

For every finite p>2 and every r<p/2, actual real potentials arbitrarily
near zero have squared gaps, the signed lattice row, and the literal
midpoint-quotient supremum in ℓ(p/2) but outside ℓʳ. One source and one
constructed original isolating family realize all three assertions.
This does not reinstate the separately refuted printed remainder formula.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- A Banach exponent between the proposed stronger exponent and the
sharp half exponent also absorbs the exact quarter-exponent remainder. -/
theorem exists_intermediate_sharpness_exponent (hp : p ≠ ⊤) (hp2 : 2 < p)
    (hr : r < p/2) : ∃ q : ℝ≥0∞, r < q ∧ 1 < q ∧ q ≠ ⊤ ∧ p/4 ≤ q ∧ q < p/2 := by
  have hhf : p/2 ≠ ⊤ := ENNReal.div_ne_top hp (by norm_num)
  have hh1 : 1 < p/2 := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    simpa using hp2
  have h4h : p/4 < p/2 := by
    apply (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hp (by norm_num)) hhf).mp
    rw [ENNReal.toReal_div,ENNReal.toReal_div]
    norm_num only [ENNReal.toReal_ofNat]
    have hpR : 0 < p.toReal := ENNReal.toReal_pos (by exact (lt_trans (by norm_num) hp2).ne') hp
    linarith
  obtain ⟨q,hlo,hhi⟩ := exists_between (max_lt hr (max_lt hh1 h4h))
  exact ⟨q,(le_max_left _ _).trans_lt hlo,
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hlo,
    ne_top_of_le_ne_top hhf hhi.le,
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hlo.le,hhi⟩

/-- Full optimality, including proposed exponents at or below one.
The source can be made arbitrarily small in the original ℓᵖ topology. -/
theorem sourceRemark10_9_halfExponent_optimal
    (hp : p ≠ ⊤) (hp2 : 2 < p) (hr : r < p/2)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hzero : (0 : CoeffPair p) ∈ U) :
    ∃ ψ : CoeffPair p, ψ ∈ U ∧ IsRealType (CoeffPair.toMax p ψ) ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ (0 : CoeffPair p) ∈ V ∧ ψ ∈ V ∧
        ∃ D c, SourceIsolatingNeighborhoods hp (lt_trans (by norm_num) hp2) V D c ∧
          (Memℓp (fun n : ℤ => (sourcePeriodicGapDisplacement hp (lt_trans (by norm_num) hp2) ψ n)^2) (p/2) ∧
            ¬ Memℓp (fun n : ℤ => (sourcePeriodicGapDisplacement hp (lt_trans (by norm_num) hp2) ψ n)^2) r) ∧
          (Memℓp (sourceRemark10_9LatticeTerm hp (lt_trans (by norm_num) hp2) ψ) (p/2) ∧
            ¬ Memℓp (sourceRemark10_9LatticeTerm hp (lt_trans (by norm_num) hp2) ψ) r) ∧
          (Memℓp (fun n : ℤ => (sourceMidpointQuotientSup hp (lt_trans (by norm_num) hp2) D ψ n : ℂ)) (p/2) ∧
            ¬ Memℓp (fun n : ℤ => (sourceMidpointQuotientSup hp (lt_trans (by norm_num) hp2) D ψ n : ℂ)) r) := by
  let hp1 : 1 < p := lt_trans (by norm_num) hp2
  obtain ⟨q,hrq,hq1,hq,h4q,hqp⟩ := exists_intermediate_sharpness_exponent hp hp2 hr
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans hq1).ne' hq
  obtain ⟨N,ε,_,_,V,hV,_,hzeroV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 0 (by simp)
  have hc := continuousAt_sourcePeriodicMidpointDisplacement_of_realType hp hp1 0 (by simp)
  obtain ⟨δ,hδ,hsmall⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  obtain ⟨ψ,hψ,hreal,hbad⟩ := exists_near_zero_real_source_squaredGap_not_memℓp hp hp1 hqr hqp
    (U ∩ (V ∩ ball 0 δ)) (hU.inter (hV.inter isOpen_ball)) ⟨hzero,hzeroV,mem_ball_self hδ⟩
  have hmid : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1 := by
    have hs := hsmall (mem_ball.mp hψ.2.2)
    rw [sourcePeriodicMidpointDisplacement_zero_source hp hp1,dist_zero_right] at hs
    exact hs.le
  refine ⟨ψ,hψ.1,hreal,V,hV,hzeroV,hψ.2.1,_,c,hD,?_,?_,?_⟩
  · constructor
    · simpa only [sourcePeriodicGapDisplacement_apply] using memℓp_sourcePeriodicSquaredGap hp hp1 ψ
    · intro hs
      exact hbad (hs.of_exponent_ge hrq.le)
  · constructor
    · obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
      have hm : Memℓp (fun n => S n) (p/2) := by
        simpa only [Coeff.halfExponent_eq_div hp] using! lp.memℓp S
      convert hm using 1
      funext n
      exact (sourceRemark10_9LatticeTerm_eq_physicalRow hp hp1 ψ hreal n).trans (hS n).2.symm
    · intro hs
      apply hbad
      apply memℓp_squared_sourceGap_of_physicalRows hp hp1 hqr ψ
      convert hs.of_exponent_ge hrq.le using 1
      funext n
      exact (sourceRemark10_9LatticeTerm_eq_physicalRow hp hp1 ψ hreal n).symm
  · refine ⟨hD.memℓp_midpointQuotientSup_half hp2 ψ hψ.2.1,?_⟩
    intro hs
    exact hbad (hD.memℓp_squaredGap_of_midpointQuotientSup hq1 hq h4q ψ hψ.2.1 hreal hmid
      (hs.of_exponent_ge hrq.le))

end NLS.ZakharovShabat
