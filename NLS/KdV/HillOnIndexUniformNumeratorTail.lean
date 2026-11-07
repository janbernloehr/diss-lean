import NLS.KdV.HillAbelianUniformNumeratorTail
import NLS.ZakharovShabat.SourceAngularOriginalDiagonalBound

/-! The actual diagonal Hill forcing g_nn-i is uniformly bounded on
fixed distant circles, before ALL n. Both signed numerator terms are
retained; no ordinary Dirichlet terminal or product constant is used. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_onIndexAbelianNumerator_tail_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+, K < (n:ℕ) →
        ∀ w ∈ sphere ((Real.pi:ℂ)*(n:ℕ)) (3*Real.pi/32),
          ‖P.abelianGapNumerator n n (w,a)-I‖ ≤ C := by
  have hdom : P.sourcePsi q ∈ P.parent.family.domain := (P.parent.subset (P.subset hq)).2
  obtain ⟨Ud,hUd,hqd,_,Md,hMd,hdnum⟩ := H.angular_original_diagonal_bound P.isolating P.V_open
    (P.sourcePsi q) hdom (P.image q hq).2
  obtain ⟨Uχ,hUχ,hqχ,_,M,hM,hχ⟩ := H.angular_original_chi_bound P.isolating P.V_open
    (P.sourcePsi q) hdom (P.image q hq).2
  obtain ⟨Ur,hUr,hqr,_,A,hA,hroots⟩ := H.angular_extension.exists_local_uniform_retainedRoot_displacement_bound
    (P.sourcePsi q) hdom
  obtain ⟨Kg,Ug,hUg,hqg,hg⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail (by norm_num) (by norm_num) (P.sourcePsi q)
  obtain ⟨Kd,hd⟩ := P.isolating.tail
  let V := (Ud ∩ Uχ) ∩ (Ur ∩ Ug)
  let U := P.source ∩ P.sourcePsi ⁻¹' V
  let ρ := 3*Real.pi/32
  let B := (A+ρ)*M/Real.pi
  let C := Md+B+1
  have hB : 0 < B := by dsimp only [B,ρ]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hU : IsOpen U := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open
    ((hUd.inter hUχ).inter (hUr.inter hUg))
  refine ⟨U,hU,⟨hq,⟨⟨hqd,hqχ⟩,hqr,hqg⟩⟩,inter_subset_left,max Kd Kg,C,hC,?_⟩
  intro a ha n hn w hw
  have hnKd : Kd < (n:ℕ) := (le_max_left _ _).trans_lt hn
  have hnKg : Kg ≤ (n:ℕ) := ((le_max_right _ _).trans_lt hn).le
  have hdisc : P.discs ((n:ℕ):ℤ) = ball ((Real.pi:ℂ)*(n:ℕ)) (Real.pi/4) :=
    hd _ (by simpa using hnKd)
  have hdiscneg : P.discs (-((n:ℕ):ℤ)) = ball (-((Real.pi:ℂ)*(n:ℕ))) (Real.pi/4) := by
    simpa only [refinedResonantDisk,Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast,mul_neg] using
      hd (-((n:ℕ):ℤ)) (by simpa using hnKd)
  have hwD : w ∈ P.discs ((n:ℕ):ℤ) := by
    rw [hdisc]
    exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  have hnD : -w ∈ P.discs (-((n:ℕ):ℤ)) := by
    rw [hdiscneg,mem_ball,dist_neg_neg]
    exact mem_ball.mpr ((mem_sphere.mp hw).trans_lt (by nlinarith [Real.pi_pos]))
  have hgap : sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ) ⊆
      ball ((Real.pi:ℂ)*(n:ℕ)) (Real.pi/16) := by
    obtain ⟨hmid,hgap⟩ := hg (P.sourcePsi a) ha.2.2.2 ((n:ℕ):ℤ) (by simpa using hnKg)
    simp only [Int.cast_natCast] at hmid
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    nlinarith [Real.pi_pos]
  have hz : w ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi a) := by
    let D := P.isolating.periodCircle (P.sourcePsi a) (P.image a ha.1).2 ((n:ℕ):ℤ)
      (P.centers ((n:ℕ):ℤ)) (P.radii ((n:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
    intro j hj
    by_cases he : j = ((n:ℕ):ℤ)
    · subst j
      have hh := mem_ball.mp (hgap hj)
      rw [mem_sphere.mp hw] at hh
      nlinarith [Real.pi_pos]
    · exact D.closedBall_subset_omittedDomain (ball_subset_closedBall ((P.discs_eq _).symm ▸ hwD)) j he hj
  have hnegne : -((n:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by have := n.pos; omega
  have hroot : ‖displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) (-((n:ℕ):ℤ))+w‖ ≤ A+ρ := by
    have h := norm_add_le (displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) (-((n:ℕ):ℤ))+(Real.pi:ℂ)*(n:ℕ))
      (w-(Real.pi:ℂ)*(n:ℕ))
    have hwρ : ‖w-(Real.pi:ℂ)*(n:ℕ)‖ = ρ := by simpa only [mem_sphere,dist_eq_norm] using hw
    rw [add_add_sub_cancel,hwρ] at h
    have hr := hroots (P.sourcePsi a) ha.2.2.1 ((n:ℕ):ℤ) (-((n:ℕ):ℤ)) hnegne
    simp only [Int.cast_neg,Int.cast_natCast,mul_neg,sub_neg_eq_add] at hr
    exact h.trans (add_le_add hr le_rfl)
  have href : SourcePeriodicReflection (by norm_num) (by norm_num) (P.sourcePsi a) :=
    sourcePeriodicReflection_hillMiuraDiagonal (P.parent.parent.miuraBall.actionBall.lift a)
  have hoff : ‖sourceAngularGapNumerator (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((n:ℕ):ℤ))
      P.parent.family.roots (P.sourcePsi a) (-w)‖ ≤ B := by
    rw [sourceAngularGapNumerator_eq_midpointFilledRegularFactor (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) (-((n:ℕ):ℤ)) hnegne _ _ (-w) (href.neg_mem_rootDomain_iff w |>.mpr hz)]
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_intCast,sub_neg_eq_add]
    push_cast
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℕ)+(n:ℕ))]
    have hnreal : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast n.pos
    calc
      _ ≤ (A+ρ)*M/(Real.pi*((n:ℕ)+(n:ℕ):ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul hroot
          (hχ _ ha.2.1.2 _ _ hnegne (-w) hnD) (norm_nonneg _) (by dsimp only [ρ]; positivity)) (by positivity)
      _ ≤ B := div_le_div_of_nonneg_left (by positivity) Real.pi_pos (by nlinarith [Real.pi_pos])
  rw [P.abelianGapNumerator_eq_signed_difference n n a ha.1 w hz]
  calc
    _ = ‖(sourceAngularGapNumerator (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((n:ℕ):ℤ)
        P.parent.family.roots (P.sourcePsi a) w-I)-
        sourceAngularGapNumerator (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((n:ℕ):ℤ))
        P.parent.family.roots (P.sourcePsi a) (-w)‖ := by congr 1; ring
    _ ≤ _ := norm_sub_le _ _
    _ ≤ Md+B := add_le_add (hdnum _ ha.2.1.1 _ w hwD) hoff
    _ ≤ C := by dsimp only [C]; linarith

end NLS.KdV.HillProductEquationPatch
