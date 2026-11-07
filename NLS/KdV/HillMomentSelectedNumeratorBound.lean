import NLS.KdV.HillAbelianReflectedCircleChart
import NLS.KdV.HillAbelianSignedNumeratorBound
import NLS.KdV.MiuraHillPsiOriginalEstimates
import NLS.KdV.HillMomentGapNumeratorTail

/-! Uniform numerator-row control on one actual selected gap, including
low and collapsed gaps. Maximum modulus retains both signed factors. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_selected_abelianGapNumerator_gap_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.source ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+, m ≠ n →
        ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) (P.sourcePsi a) (m:ℤ),
          ‖P.abelianGapNumerator n m (z,a)‖ ≤
            C*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨c,r,ρ,hrpos,hrρ,hclosed,Ug,hUg,hqg,hgP,hgeom⟩ := P.exists_reflected_abelian_circle_chart m q hq hr
  have hdom : P.sourcePsi q ∈ P.parent.family.domain := (P.parent.subset (P.subset hq)).2
  obtain ⟨Uχ,hUχ,hqχ,_,M,hM,hχ⟩ := H.angular_original_chi_bound P.isolating P.V_open
    (P.sourcePsi q) hdom (P.image q hq).2
  obtain ⟨Ur,hUr,hqr,_,A,hA,hroots⟩ := H.angular_extension.exists_local_uniform_retainedRoot_displacement_bound
    (P.sourcePsi q) hdom
  let V := P.source ∩ P.sourcePsi ⁻¹' (Uχ ∩ Ur)
  have hV : IsOpen V := P.analytic_sourcePsi.continuousOn.isOpen_inter_preimage P.source_open (hUχ.inter hUr)
  let B := A+‖(Real.pi:ℂ)*(m:ℕ)-c‖+ρ
  let D := B*M/Real.pi
  have hρ : 0 < ρ := hrpos.trans hrρ
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨Ug ∩ V,hUg.inter hV,⟨hqg,hq,hqχ,hqr⟩,(fun a ha => ha.2.1),D,hD,?_⟩
  intro a ha n hmn z hzGap
  let k : ℝ := 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hball (w : ℂ) (hw : w ∈ sphere c ρ) := hclosed w (sphere_subset_closedBall hw)
  have hz : sphere c ρ ⊆ sourceCanonicalRootDomain (by norm_num) (by norm_num) (P.sourcePsi a) := by
    apply sourceCanonicalRootDomain_of_enclosingCircle (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ) c ρ
      ((hgeom a ha.1).1.trans (ball_subset_ball hrρ.le))
    intro w hw
    let E := P.isolating.periodCircle (P.sourcePsi a) (P.image a ha.2.1).2 ((m:ℕ):ℤ)
      (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
    exact E.closedBall_subset_omittedDomain (ball_subset_closedBall (hclosed w hw).1)
  have hmne : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
  have hnegne : -((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by have := n.pos; have := m.pos; omega
  have hdist (w : ℂ) (hw : w ∈ sphere c ρ) : ‖w-(Real.pi:ℂ)*(m:ℕ)‖ ≤ ‖(Real.pi:ℂ)*(m:ℕ)-c‖+ρ := by
    have h := norm_add_le (w-c) (c-(Real.pi:ℂ)*(m:ℕ))
    have hwρ : ‖w-c‖ = ρ := by simpa only [mem_sphere,dist_eq_norm] using hw
    rw [sub_add_sub_cancel,hwρ,norm_sub_rev c] at h
    linarith
  have hnum (w : ℂ) (hw : w ∈ sphere c ρ) : ‖P.abelianGapNumerator n m (w,a)‖ ≤ D*k := by
    apply P.norm_abelianGapNumerator_le_of_signed_bounds n m hmn a ha.2.1 w (hz hw) B M hB.le
    · have h := norm_sub_le (displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) ((m:ℕ):ℤ)-(Real.pi:ℂ)*(m:ℕ))
        (w-(Real.pi:ℂ)*(m:ℕ))
      rw [sub_sub_sub_cancel_right] at h
      have hb := hroots (P.sourcePsi a) ha.2.2.2 ((n:ℕ):ℤ) ((m:ℕ):ℤ) hmne
      simp only [Int.cast_natCast] at hb
      have he := h.trans (add_le_add hb (hdist w hw))
      simpa only [B,add_assoc] using he
    · have h := norm_add_le (displacedRoots (P.parent.family.roots ((n:ℕ):ℤ) (P.sourcePsi a):Coeff 2) (-((m:ℕ):ℤ))+(Real.pi:ℂ)*(m:ℕ))
        (w-(Real.pi:ℂ)*(m:ℕ))
      rw [add_add_sub_cancel] at h
      have hb := hroots (P.sourcePsi a) ha.2.2.2 ((n:ℕ):ℤ) (-((m:ℕ):ℤ)) hnegne
      simp only [Int.cast_neg,Int.cast_natCast,mul_neg,sub_neg_eq_add] at hb
      have he := h.trans (add_le_add hb (hdist w hw))
      simpa only [B,add_assoc] using he
    · exact hχ _ ha.2.2.1 _ _ hmne w ((P.discs_eq _).symm ▸ (hball w hw).1)
    · exact hχ _ ha.2.2.1 _ _ hnegne (-w) ((P.discs_eq _).symm ▸ (hball w hw).2)
  apply P.norm_abelianGapNumerator_le_of_circle_bound n m a ha.2.1 c ρ hρ
    (fun w hw => ball_subset_closedBall (hclosed w hw).1) (D*k) hnum z
  exact ball_subset_closedBall (ball_subset_ball hrρ.le ((hgeom a ha.1).1 hzGap))

end NLS.KdV.HillProductEquationPatch
