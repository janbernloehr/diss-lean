import NLS.KdV.HillAbelianUniformNumeratorTail
import NLS.KdV.HillAbelianJointFrequencyDomain
import NLS.ComplexAnalysis.LocalTwoRootQuotient

/-! Maximum modulus transfers the actual all-row numerator estimate
from fixed tail circles to the whole moving complex gap. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem norm_abelianGapNumerator_le_of_circle_bound (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hdisc : closedBall c r ⊆ closedBall (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ)))
    (B : ℝ) (hb : ∀ w ∈ sphere c r, ‖P.abelianGapNumerator n m (w,q)‖ ≤ B)
    (z : ℂ) (hz : z ∈ closedBall c r) : ‖P.abelianGapNumerator n m (z,q)‖ ≤ B := by
  apply norm_le_of_sphere_bound_of_analyticOnNhd c hr (B := B) (z := z)
  · intro w hw
    exact (P.analytic_abelianGapNumerator_on_patch n m (w,q) ⟨hdisc hw,hq⟩).comp
      (f := fun x : ℂ => (x,q)) (analyticAt_id.prod analyticAt_const)
  · exact hb
  · simpa only [mem_closedBall,dist_eq_norm] using hz

theorem exists_local_uniform_abelianGapNumerator_gap_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ a ∈ U, ∀ n m : ℕ+, K < (m:ℕ) → m ≠ n →
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
          ‖P.abelianGapNumerator n m (z,a)‖ ≤
            B*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨Un,hUn,hqn,hnP,Kn,B,hB,hnum⟩ :=
    P.exists_local_uniform_abelianGapNumerator_tail_bound H q hq
  obtain ⟨Kg,Ug,hUg,hqg,hg⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail
    (p := 2) (by simp) (by norm_num) (P.sourcePsi q)
  obtain ⟨Kd,hd⟩ := P.isolating.tail
  let V := P.source ∩ P.sourcePsi ⁻¹' Ug
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hUg
  refine ⟨Un ∩ V,hUn.inter hV,⟨hqn,hq,hqg⟩,fun a ha => hnP ha.1,
    max Kn (max Kg Kd),B,hB,?_⟩
  intro a ha n m hm hmn z hz
  have hmKn : Kn < (m:ℕ) := (le_max_left _ _).trans_lt hm
  have hmKg : Kg ≤ (m:ℕ) := ((le_max_left Kg Kd).trans (le_max_right Kn _)).trans hm.le
  have hmKd : Kd < (m:ℕ) := ((le_max_right Kg Kd).trans (le_max_right Kn _)).trans_lt hm
  have hdisc : P.discs (m:ℤ)=ball ((Real.pi:ℂ)*(m:ℕ)) (Real.pi/4) :=
    hd _ (by simpa using hmKd)
  have hgap : sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ) ⊆
      ball ((Real.pi:ℂ)*(m:ℕ)) (Real.pi/16) := by
    obtain ⟨hmid,hgap⟩ := hg (P.sourcePsi a) ha.2.2 (m:ℤ) (by simpa using hmKg)
    simp only [Int.cast_natCast] at hmid
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    nlinarith [Real.pi_pos]
  apply P.norm_abelianGapNumerator_le_of_circle_bound n m a (hnP ha.1)
    ((Real.pi:ℂ)*(m:ℕ)) (3*Real.pi/32) (by positivity) (B :=
      B*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
  · intro w hw
    apply ball_subset_closedBall
    rw [← P.discs_eq,hdisc]
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  · exact hnum a ha.1 n m hmKn hmn
  · exact ball_subset_closedBall (ball_subset_ball (by nlinarith [Real.pi_pos]) (hgap hz))

end NLS.KdV.HillProductEquationPatch
