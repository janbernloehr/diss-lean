import NLS.KdV.HillOnIndexUniformNumeratorTail
import NLS.KdV.HillOnIndexCircleBound
import NLS.ZakharovShabat.SourceEnclosedGapDisplacementBound
import NLS.SequenceSpaces.LocallyUniformCoordinates

/-! The ACTUAL diagonal remainder at the AUXILIARY divisor is uniformly
bounded for ALL high indices on ONE native complex source neighborhood.
The filled equation and enclosing circle include complex collapsed gaps. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalOnIndexAbelianCorrection_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ m : ℕ+, K < (m:ℕ) →
        ‖P.physicalOnIndexAbelianCorrection m a‖ ≤ C := by
  obtain ⟨Un,hUn,hqn,_,Kn,B,hB,hnum⟩ := P.exists_local_uniform_onIndexAbelianNumerator_tail_bound H q hq.1
  let μ : PeriodOneHminusOne → Coeff 2 := fun a => hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift a)
  have hμ : AnalyticAt ℂ μ q := P.parent.parent.analytic_auxiliaryDisplacement q (P.parent.subset (P.subset hq.1)).1
  obtain ⟨Kμ,Uμ,hUμ,hqμ,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
    μ q hμ.continuousAt (Real.pi/16) (by positivity)
  obtain ⟨Kg,Ug,hUg,hqg,hg⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (P.sourcePsi q)
  obtain ⟨Kd,hd⟩ := P.isolating.tail
  let V := P.source ∩ P.sourcePsi ⁻¹' Ug
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open hUg
  let U := (Un ∩ Uμ) ∩ (V ∩ P.physicalDirichletSource)
  let r := Real.pi/16
  let ρ := 3*Real.pi/32
  let C := (3*r)*(Real.pi*ρ^2*B/(ρ-r)^3)
  have hrρ : r < ρ := by dsimp only [r,ρ]; nlinarith [Real.pi_pos]
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hC : 0 < C := by dsimp only [C,r]; have := sub_pos.mpr hrρ; positivity
  refine ⟨U,(hUn.inter hUμ).inter (hV.inter P.physicalDirichletSource_open),
    ⟨⟨hqn,hqμ⟩,⟨⟨hq.1,hqg⟩,hq⟩⟩,(fun a ha => ha.2.2),max (max Kn Kμ) (max Kg Kd),C,hC,?_⟩
  intro a ha m hm
  have hleft : max Kn Kμ < (m:ℕ) := (le_max_left _ _).trans_lt hm
  have hright : max Kg Kd < (m:ℕ) := (le_max_right _ _).trans_lt hm
  have hmKn : Kn < (m:ℕ) := (le_max_left _ _).trans_lt hleft
  have hmKμ : Kμ < (m:ℕ) := (le_max_right _ _).trans_lt hleft
  have hmKg : Kg ≤ (m:ℕ) := ((le_max_left _ _).trans_lt hright).le
  have hmKd : Kd < (m:ℕ) := (le_max_right _ _).trans_lt hright
  let c : ℂ := (Real.pi:ℂ)*(m:ℕ)
  have hρD : closedBall c ρ ⊆ ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ)) := by
    rw [← P.discs_eq,hd _ (by simpa using hmKd)]
    intro w hw
    exact mem_ball.mpr ((mem_closedBall.mp hw).trans_lt (by dsimp only [ρ]; nlinarith [Real.pi_pos]))
  have hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ) ⊆ ball c r := by
    obtain ⟨hmid,hgap⟩ := hg (P.sourcePsi a) ha.2.1.2 ((m:ℕ):ℤ) (by simpa using hmKg)
    simp only [Int.cast_natCast] at hmid
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    dsimp only [c,r]
    nlinarith [Real.pi_pos]
  have hterminal : P.physicalDirichletFrequency ((m:ℕ):ℤ) a ∈ closedBall c r := by
    have h := hsmall a ha.1.2 ((m:ℕ):ℤ) (by simpa using hmKμ)
    simpa only [μ,hillMiuraDirichletDisplacement_apply,physicalDirichletFrequency,Int.cast_natCast,
      mem_closedBall,dist_eq_norm,c,r] using h.le
  have hbound (w : ℂ) (hw : w ∈ sphere c ρ) : ‖P.abelianGapNumerator m m (w,a)-I‖ ≤ B :=
    hnum a ha.1.1 m hmKn w hw
  have hv := P.norm_physicalOnIndexAbelianCorrection_le_of_circle_bound m a ha.2.2 c r ρ B
    hρ hrρ hρD hB.le hgap hbound hterminal
  exact hv.trans (mul_le_mul_of_nonneg_right
    (norm_sub_midpoint_add_halfGap_le_of_enclosed (by norm_num) (by norm_num)
      (P.sourcePsi a) ((m:ℕ):ℤ) c _ r hgap hterminal) (by positivity))

end NLS.KdV.HillProductEquationPatch
