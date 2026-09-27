import NLS.ZakharovShabat.SourcePsiFreeQuotientTail
import NLS.SequenceSpaces.UniformTailContinuity

/-!
# Continuity of the free-source quotient error in `ℓᵖ`

The quantitative tail estimate is uniform in a small root-displacement
ball. Each of the finitely many remaining quotient coordinates is
analytic. The locally uniform tail criterion therefore upgrades
coordinatewise continuity to continuity in the `ℓᵖ` norm at zero.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Each free-center quotient error is continuous in the
root-displacement sequence at zero. -/
theorem continuousAt_sourcePsiFreeQuotientError_coordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) :
    ContinuousAt (fun a : Coeff p =>
      sourcePsiFreeQuotientError hp hp1 a m) 0 := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hzero : (0 : CoeffPair p) ∈ W :=
    hreal (by simp [realTypeSourceLocus])
  have hdomain : (Real.pi : ℂ)*m ∈
      sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) m := by
    intro k hkm
    rw [sourcePeriodicSegment_zero_source hp hp1 k]
    intro he
    exact (freeCenter_not_mem_closedBall_other m k (Ne.symm hkm)
      0 Real.pi_pos) (he ▸ mem_closedBall_self le_rfl)
  have hQ : AnalyticAt ℂ
      (sourceSingleRootQuotientJointProduct hp hp1 m)
      (((Real.pi : ℂ)*m),((0 : Coeff p),(0 : CoeffPair p))) :=
    (hdata m).2 _ ⟨hzero,hdomain⟩
  have hmap : AnalyticAt ℂ
      (fun a : Coeff p =>
        (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))) 0 :=
    analyticAt_const.prod (analyticAt_id.prod analyticAt_const)
  have hcont : ContinuousAt (fun a : Coeff p =>
      sourceSingleRootQuotientJointProduct hp hp1 m
        (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))) 0 :=
    (hQ.comp (f := fun a : Coeff p =>
      (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))) hmap).continuousAt
  change ContinuousAt (fun a : Coeff p =>
    sourceSingleRootQuotientJointProduct hp hp1 m
      (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1) 0
  convert hcont.sub continuousAt_const using 1
  funext a
  rfl

/-- The quotient-error map is continuous at the free displacement in
the sequence norm, not merely at each spectral index. -/
theorem continuousAt_sourcePsiFreeQuotientError_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ContinuousAt (sourcePsiFreeQuotientError hp hp1)
      (0 : Coeff p) := by
  apply Coeff.continuousAt_of_coordinatewise_of_uniform_tails
  · intro m
    exact continuousAt_sourcePsiFreeQuotientError_coordinate hp hp1 m
  · intro ε hε
    obtain ⟨K,A,D,hmajor⟩ :=
      exists_sourcePsiQuotient_freeCenter_tailMajorant_norm hp hp1
    let G : Coeff p → ℝ := fun a =>
      A*‖a‖ + Real.exp (D*‖a‖)*(D*‖a‖)^2
    have hG : ContinuousAt G (0 : Coeff p) := by
      dsimp [G]
      fun_prop
    have hGzero : G (0 : Coeff p) = 0 := by simp [G]
    obtain ⟨δ,hδ,hGδ⟩ := Metric.continuousAt_iff.mp hG ε hε
    let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
    let V : Set (Coeff p) := ball 0 δ
    refine ⟨s,V,isOpen_ball,mem_ball_self hδ,?_⟩
    intro a ha
    obtain ⟨B,hpoint,hB⟩ := hmajor a
    have hGa : G a < ε := by
      have hdist := hGδ (mem_ball.mp ha)
      rw [hGzero,Real.dist_eq,sub_zero] at hdist
      exact lt_of_le_of_lt (le_abs_self _) hdist
    have htail :
        ‖sourcePsiFreeQuotientError hp hp1 a -
            Coeff.truncate s (sourcePsiFreeQuotientError hp hp1 a)‖ ≤
          ‖B‖ := by
      apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
      intro m
      by_cases hm : m ∈ s
      · simp [Coeff.truncate_apply,hm]
      · have hmK : K ≤ m.natAbs := by
          simp only [s,Finset.mem_Icc] at hm
          omega
        simpa [Coeff.truncate_apply,hm,
          sourcePsiFreeQuotientError_apply] using hpoint m hmK
    exact (htail.trans hB).trans hGa.le

end NLS.ZakharovShabat
