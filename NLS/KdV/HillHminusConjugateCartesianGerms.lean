import NLS.KdV.HillHminusCartesianGerms

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillSpectralCartesian_conj_eq_action_div
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hne : hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos ≠ 0) :
    conj (hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos) =
      (2 * (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ)) /
        hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos := by
  apply (eq_div_iff hne).mpr
  have hi := hillSpectralCartesian_action_identity (by simp) (by simp [IsRealHillPotential])
    q.val q.property.1 q.property.2 n n.pos
  apply Complex.ext
  · simpa only [mul_re,conj_re,conj_im,neg_mul,sub_neg_eq_add,ofReal_re,ofReal_im,
      mul_zero,sub_zero,show (2:ℂ).re=2 from rfl,show (2:ℂ).im=0 from rfl,←sq,zero_pow (by decide : (2:ℕ)≠0),sub_zero] using hi
  · simp only [mul_im,conj_re,conj_im,ofReal_im,show (2:ℂ).im=0 from rfl,
      show (2:ℂ).re=2 from rfl,zero_mul,mul_zero,add_zero]
    ring

/-- The conjugate ORIGINAL Cartesian coordinate also has a common genuine
holomorphic H-minus-one germ along the original isospectral set. It is
constructed as twice the ORIGINAL action divided by the ORIGINAL coordinate,
not by pointwise antiholomorphic conjugation of the complex extension. -/
theorem exists_hillOriginal_conjugate_cartesian_hminus_isospectral_physical_germs
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ C (ball (hillOriginalHminusSource q.val) ρ) ∧
      ∀ p : RealPeriodOneHillPotential,
        hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ρ →
        (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
          hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) →
        ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ p ∈ V ∧
          ∀ r ∈ V, C (hillOriginalHminusSource r.val) =
            conj (hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos) := by
  obtain ⟨ε,hε,Z,hZ,hZM⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q n hgap
  obtain ⟨U,hU,hqU,hA,hAM⟩ :=
    exists_hillHminusRelativeAction_isospectral_physical_germs q n n.pos
  let A := hillHminusRelativeAction q.val q.property.1 q.property.2 n
  obtain ⟨V0,_,hq0,hZ0⟩ := hZM q (mem_ball_self hε) (fun _ => rfl)
  have hZq := hZ0 q hq0
  have hnonzero : Z (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hZq]
    intro he
    have hi := hillSpectralCartesian_action_identity (by simp) (by simp [IsRealHillPotential])
      q.val q.property.1 q.property.2 n n.pos
    rw [he,zero_re,zero_im] at hi
    have hz : hillRealGapIntegral q.val q.property.1 q.property.2 n 0 = 0 := by nlinarith
    have hnot : ¬ hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)-1) <
        hillRealLabels q.val q.property.1 q.property.2 (2*(n:ℕ)) := by
      rw [←hillRealGapIntegral_pos_iff q.val q.property.1 q.property.2 n n.pos,hz]
      exact lt_irrefl 0
    have heq := le_antisymm
      (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega : 2*(n:ℕ)-1≤2*(n:ℕ)))
      (le_of_not_gt hnot)
    exact hgap (by simp only [hillRealGapHalfLength,heq,sub_self,zero_div])
  let D := (ball (hillOriginalHminusSource q.val) ε ∩ Z ⁻¹' ({0} : Set ℂ)ᶜ) ∩ U
  have hD : IsOpen D :=
    (hZ.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton).inter hU
  have hqD : hillOriginalHminusSource q.val ∈ D := ⟨⟨mem_ball_self hε,hnonzero⟩,hqU⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hD _ hqD
  let C : PeriodOneHminusOne → ℂ := fun a => 2 * A a / Z a
  refine ⟨ρ,hρ,C,?_,?_⟩
  · intro a ha
    exact (analyticAt_const.mul (hA a (hball ha).2)).div
      (hZ a (hball ha).1.1) (hball ha).1.2
  · intro p hp hΔ
    obtain ⟨V,hV,hpV,hZp⟩ := hZM p (hball hp).1.1 hΔ
    obtain ⟨W,hW,hpW,hAp⟩ := hAM p hΔ
    let T : Set RealPeriodOneHillPotential :=
      (fun r : RealPeriodOneHillPotential => hillOriginalHminusSource r.val) ⁻¹'
        ball (hillOriginalHminusSource q.val) ρ
    have hT : IsOpen T := isOpen_ball.preimage
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val)
    refine ⟨(V ∩ W) ∩ T,(hV.inter hW).inter hT,⟨⟨hpV,hpW⟩,hp⟩,?_⟩
    intro r hr
    have hne : hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos ≠ 0 := by
      rw [←hZp r hr.1.1]
      exact (hball hr.2).1.2
    change 2 * A (hillOriginalHminusSource r.val) / Z (hillOriginalHminusSource r.val) = _
    dsimp only [A]
    rw [hAp r hr.1.2,hZp r hr.1.1]
    exact (hillSpectralCartesian_conj_eq_action_div r n hne).symm

end NLS.KdV
