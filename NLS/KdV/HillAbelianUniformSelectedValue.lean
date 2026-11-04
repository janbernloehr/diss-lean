import NLS.KdV.HillAbelianReflectedCircleChart
import NLS.KdV.HillAbelianSignedNumeratorBound
import NLS.KdV.MiuraHillPsiOriginalEstimates

/-! The ACTUAL physical value at a fixed selected gap has a reciprocal
signed-index bound uniform over EVERY numerator index on one complex
neighborhood of a real native source. Low and collapsed gaps are included. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_selected_physicalOffIndexAbelianValue_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+, m ≠ n →
        ‖P.physicalOffIndexAbelianValue n m a‖ ≤ C*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
          (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
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
  let C := Real.pi*ρ^2*D/(ρ-r)^3
  have hρ : 0 < ρ := hrpos.trans hrρ
  have hB : 0 < B := by dsimp only [B]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; have := sub_pos.mpr hrρ; positivity
  refine ⟨Ug ∩ V,hUg.inter hV,⟨hqg,hq,hqχ,hqr⟩,(fun a ha => hgP ha.1),C,hC,?_⟩
  intro a ha n hmn
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
  have hv := P.norm_physicalOffIndexAbelianValue_le_of_circle_bound n m hmn a (hgP ha.1) c r ρ (D*k)
    hρ hrρ (fun w hw => (hclosed w hw).1) (mul_nonneg hD.le hk) (hgeom a ha.1).1 hnum (hgeom a ha.1).2
  have hw : ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖/2 ≤
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
      ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖ := by
    nlinarith [norm_nonneg (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ))]
  apply hv.trans
  calc
    _ ≤ (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
      ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
        (Real.pi*ρ^2*(D*k)/(ρ-r)^3) := mul_le_mul_of_nonneg_right hw (by positivity)
    _ = _ := by dsimp only [C,k]; ring

end NLS.KdV.HillProductEquationPatch
