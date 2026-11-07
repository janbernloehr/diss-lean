import NLS.KdV.HillMomentGapNumeratorTail
import NLS.KdV.HillOnIndexUniformNumeratorTail
import NLS.KdV.HillAbelianReflectedCircleChart
import NLS.ComplexAnalysis.CompactParameterBounds

/-! Actual diagonal gap numerators are locally bounded on every fixed
gap and, uniformly before all indices, on the entire tail gaps. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_selected_diagonal_abelianGapNumerator_gap_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ B : ℝ, 0 < B ∧ ∀ a ∈ U,
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ),
          ‖P.abelianGapNumerator m m (z,a)‖ ≤ B := by
  obtain ⟨c,r,ρ,hrpos,hrρ,hclosed,Ug,hUg,hqg,hgP,hgeom⟩ := P.exists_reflected_abelian_circle_chart m q hq hr
  let J := ball (P.centers (m:ℤ):ℂ) (P.radii (m:ℤ)) ×ˢ P.source
  have hJ : IsOpen J := isOpen_ball.prod P.source_open
  have ha : AnalyticOnNhd ℂ (P.abelianGapNumerator m m) J :=
    (P.analytic_abelianGapNumerator_on_patch m m).mono
      (fun t ht => ⟨ball_subset_closedBall ht.1,ht.2⟩)
  obtain ⟨V,hV,hqV,B,hB,hbound⟩ := exists_local_uniform_bound_on_compact_of_continuousOn
    (P.abelianGapNumerator m m) J hJ ha.continuousOn (closedBall c ρ) (isCompact_closedBall c ρ) q
    (fun w hw => ⟨(hclosed w hw).1,hq⟩)
  refine ⟨Ug ∩ V,hUg.inter hV,⟨hqg,hqV⟩,(fun a ha => (hgP ha.1).1),B+1,by positivity,?_⟩
  intro a ha z hz
  have hzK := ball_subset_closedBall (ball_subset_ball hrρ.le ((hgeom a ha.1).1 hz))
  exact (hbound a ha.2 z hzK).2.trans (by linarith)

theorem exists_local_uniform_diagonal_abelianGapNumerator_gap_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ K : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ a ∈ U, ∀ n : ℕ+, K < (n:ℕ) →
        ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (n:ℤ),
          ‖P.abelianGapNumerator n n (z,a)‖ ≤ B := by
  obtain ⟨Un,hUn,hqn,hnP,Kn,B,hB,hnum⟩ :=
    P.exists_local_uniform_onIndexAbelianNumerator_tail_bound H q hq
  obtain ⟨Kg,Ug,hUg,hqg,hg⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail
    (p := 2) (by simp) (by norm_num) (P.sourcePsi q)
  obtain ⟨Kd,hd⟩ := P.isolating.tail
  let V := P.source ∩ P.sourcePsi ⁻¹' Ug
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hUg
  refine ⟨Un ∩ V,hUn.inter hV,⟨hqn,hq,hqg⟩,fun a ha => hnP ha.1,
    max Kn (max Kg Kd),B+1,by positivity,?_⟩
  intro a ha n hn z hz
  have hnKn : Kn < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hnKg : Kg ≤ (n:ℕ) := ((le_max_left Kg Kd).trans (le_max_right Kn _)).trans hn.le
  have hnKd : Kd < (n:ℕ) := ((le_max_right Kg Kd).trans (le_max_right Kn _)).trans_lt hn
  have hdisc : P.discs (n:ℤ)=ball ((Real.pi:ℂ)*(n:ℕ)) (Real.pi/4) :=
    hd _ (by simpa using hnKd)
  have hgap : sourcePeriodicSegment (by simp) (by norm_num) (P.sourcePsi a) (n:ℤ) ⊆
      ball ((Real.pi:ℂ)*(n:ℕ)) (Real.pi/16) := by
    obtain ⟨hmid,hgap⟩ := hg (P.sourcePsi a) ha.2.2 (n:ℤ) (by simpa using hnKg)
    simp only [Int.cast_natCast] at hmid
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    nlinarith [Real.pi_pos]
  apply P.norm_abelianGapNumerator_le_of_circle_bound n n a (hnP ha.1)
    ((Real.pi:ℂ)*(n:ℕ)) (3*Real.pi/32) (by positivity) (B := B+1)
  · intro w hw
    apply ball_subset_closedBall
    rw [← P.discs_eq,hdisc]
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  · intro w hw
    have ht := norm_add_le (P.abelianGapNumerator n n (w,a)-I) I
    rw [sub_add_cancel,norm_I] at ht
    exact ht.trans (add_le_add (hnum a ha.1 n hnKn w hw) le_rfl)
  · exact ball_subset_closedBall (ball_subset_ball (by nlinarith [Real.pi_pos]) (hgap hz))

end NLS.KdV.HillProductEquationPatch
