import NLS.KdV.HillAbelianSignedNumeratorBound
import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-! One neighborhood and constant control the ACTUAL odd Hill gap
numerators on fixed tail circles BEFORE ALL numerator/selected indices.
The estimates are supplied by retained original data, not hypothesized
pointwise bounds on the canonical product scalar. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_abelianGapNumerator_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n m : ℕ+, K < (m:ℕ) → m ≠ n →
        ∀ w ∈ sphere ((Real.pi:ℂ)*(m:ℕ)) (3*Real.pi/32),
          ‖P.abelianGapNumerator n m (w,a)‖ ≤
            C*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  have hdom : P.sourcePsi q ∈ P.parent.family.domain := (P.parent.subset (P.subset hq)).2
  obtain ⟨Uχ,hUχ,hqχ,_,M,hM,hχ⟩ := H.angular_original_chi_bound P.isolating P.V_open
    (P.sourcePsi q) hdom (P.image q hq).2
  obtain ⟨Ur,hUr,hqr,_,A,hA,hroots⟩ := H.angular_extension.exists_local_uniform_retainedRoot_displacement_bound
    (P.sourcePsi q) hdom
  obtain ⟨Kg,Ug,hUg,hqg,hg⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (P.sourcePsi q)
  obtain ⟨Kd,hd⟩ := P.isolating.tail
  let V := (Uχ ∩ Ur) ∩ Ug
  let U := P.source ∩ P.sourcePsi ⁻¹' V
  let ρ := 3*Real.pi/32
  let C := (A+ρ)*M/Real.pi
  have hC : 0 < C := by dsimp only [C,ρ]; positivity
  have hU : IsOpen U := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open
    ((hUχ.inter hUr).inter hUg)
  refine ⟨U,hU,⟨hq,⟨⟨hqχ,hqr⟩,hqg⟩⟩,inter_subset_left,max Kd Kg,C,hC,?_⟩
  intro a ha n m hm hmn w hw
  have hmKd : Kd < (m:ℕ) := (le_max_left _ _).trans_lt hm
  have hmKg : Kg ≤ (m:ℕ) := ((le_max_right _ _).trans_lt hm).le
  have hdisc : P.discs ((m:ℕ):ℤ) = ball ((Real.pi:ℂ)*(m:ℕ)) (Real.pi/4) :=
    hd _ (by simpa using hmKd)
  have hdiscneg : P.discs (-((m:ℕ):ℤ)) = ball (-((Real.pi:ℂ)*(m:ℕ))) (Real.pi/4) := by
    simpa only [refinedResonantDisk,Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast,mul_neg] using
      hd (-((m:ℕ):ℤ)) (by simpa using hmKd)
  have hwD : w ∈ P.discs ((m:ℕ):ℤ) := by
    rw [hdisc]
    exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  have hnD : -w ∈ P.discs (-((m:ℕ):ℤ)) := by
    rw [hdiscneg,mem_ball,dist_neg_neg]
    exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  have hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ) ⊆
      ball ((Real.pi:ℂ)*(m:ℕ)) (Real.pi/16) := by
    obtain ⟨hmid,hgap⟩ := hg (P.sourcePsi a) ha.2.2 ((m:ℕ):ℤ) (by simpa using hmKg)
    simp only [Int.cast_natCast] at hmid
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    nlinarith [Real.pi_pos]
  have hz : w ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi a) := by
    let D := P.isolating.periodCircle (P.sourcePsi a) (P.image a ha.1).2 ((m:ℕ):ℤ)
      (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
    intro j hj
    by_cases he : j = ((m:ℕ):ℤ)
    · subst j
      have hh := mem_ball.mp (hgap hj)
      rw [mem_sphere.mp hw] at hh
      nlinarith [Real.pi_pos]
    · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall ((P.discs_eq _).symm ▸ hwD)) j he hj
  have hmne : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
  have hnegne : -((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  have hp : ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) ((m:ℕ):ℤ)-w‖ ≤ A+ρ := by
    have h := norm_sub_le (displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) ((m:ℕ):ℤ)-(Real.pi:ℂ)*(m:ℕ))
      (w-(Real.pi:ℂ)*(m:ℕ))
    have hwρ : ‖w-(Real.pi:ℂ)*(m:ℕ)‖ = ρ := by simpa only [mem_sphere,dist_eq_norm] using hw
    rw [sub_sub_sub_cancel_right,hwρ] at h
    exact h.trans (add_le_add (hroots _ ha.2.1.2 _ _ hmne) le_rfl)
  have hn : ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) (-((m:ℕ):ℤ))+w‖ ≤ A+ρ := by
    have h := norm_add_le (displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) (-((m:ℕ):ℤ))+(Real.pi:ℂ)*(m:ℕ))
      (w-(Real.pi:ℂ)*(m:ℕ))
    have hwρ : ‖w-(Real.pi:ℂ)*(m:ℕ)‖ = ρ := by simpa only [mem_sphere,dist_eq_norm] using hw
    rw [add_add_sub_cancel,hwρ] at h
    have hr := hroots (P.sourcePsi a) ha.2.1.2 ((n:ℕ):ℤ) (-((m:ℕ):ℤ)) hnegne
    simp only [Int.cast_neg,Int.cast_natCast,mul_neg,sub_neg_eq_add] at hr
    exact h.trans (add_le_add hr le_rfl)
  exact P.norm_abelianGapNumerator_le_of_signed_bounds n m hmn a ha.1 w hz (A+ρ) M (by dsimp only [ρ]; positivity)
    hp hn (hχ _ ha.2.1.1 _ _ hmne w hwD) (hχ _ ha.2.1.1 _ _ hnegne (-w) hnD)

end NLS.KdV.HillProductEquationPatch
