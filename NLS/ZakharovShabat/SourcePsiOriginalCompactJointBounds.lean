import NLS.ZakharovShabat.SourcePsiOriginalComplexJacobianCharts

/-!
# SourcePsiOriginalCompactJointBounds

One equation bound controls all compact root centers and all indices.
Cauchy gives constants 2*C/r and 4*C/r^2. A near/far comparison yields
the joint root/source estimate throughout one open tube around the
whole compact root set, for the actual original full Jacobians.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One equation bound on balls of radius 4r works at every center in
a compact root set and every deleted index, with complex source variation. -/
theorem SourceLemma12_4Data.originalEquation_compact_complex_ball_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (K : Set (Coeff p)) (hK : IsCompact K) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ a ∈ K, ∀ n : ℤ,
      ∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) (4*r),
        t.2 ∈ W ∧ ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C := by
  classical
  have hlocal (a : Coeff p) := H.originalEquation_allIndex_complex_ball_bound φ hφ a
  choose ρ B hρ hB hb using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun a : Coeff p => ball a (ρ a/2))
    (fun _ => isOpen_ball) (fun a _ => mem_iUnion.mpr ⟨a,mem_ball_self (half_pos (hρ a))⟩)
  by_cases hsnon : s.Nonempty
  · let δ := s.inf' hsnon (fun a => ρ a/2)
    let C := ∑ a ∈ s, B a
    have hδ : 0 < δ := (Finset.lt_inf'_iff hsnon).2 (fun a _ => half_pos (hρ a))
    refine ⟨δ/4,C,by positivity,Finset.sum_nonneg (fun a _ => hB a),?_⟩
    intro a ha n t ht
    obtain ⟨b,hbs,hab⟩ := mem_iUnion₂.mp (hs ha)
    have hδb : δ ≤ ρ b/2 := Finset.inf'_le _ hbs
    have hproj : dist (Coeff.deleteCoordinateTo n a) (Coeff.deleteCoordinateTo n b) ≤ dist a b := by
      rw [dist_eq_norm,dist_eq_norm,← map_sub]
      simpa only [one_mul] using (Coeff.deleteCoordinateTo (p := p) n).le_of_opNorm_le
        (Coeff.norm_deleteCoordinateTo_le_one n) (a-b)
    have hab' : dist (Coeff.deleteCoordinateTo n a,φ) (Coeff.deleteCoordinateTo n b,φ) < ρ b/2 := by
      simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hproj.trans_lt (mem_ball.mp hab)
    have ht' : t ∈ ball (Coeff.deleteCoordinateTo n b,φ) (ρ b) := by
      have hdist := dist_triangle t (Coeff.deleteCoordinateTo n a,φ) (Coeff.deleteCoordinateTo n b,φ)
      rw [mem_ball] at ht ⊢
      linarith
    have h := hb b n t ht'
    exact ⟨h.1,h.2.trans (Finset.single_le_sum (fun j _ => hB j) hbs)⟩
  · refine ⟨1,0,by norm_num,le_rfl,?_⟩
    intro a ha
    obtain ⟨b,hbs,_⟩ := mem_iUnion₂.mp (hs ha)
    exact (hsnon ⟨b,hbs⟩).elim

/-- The actual root Jacobian has the explicit first Cauchy bound 2C/r. -/
theorem norm_sourcePsiOriginalRootJacobian_le_of_joint_ball_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n × CoeffPair p) (r C : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiOriginalEquation hp hp1 n t.1 t.2) (ball a (4*r)))
    (hb : ∀ t ∈ ball a (4*r), ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C)
    {t : DeletedCoeff p n × CoeffPair p} (ht : t ∈ ball a r) :
    ‖sourcePsiOriginalRootJacobian hp hp1 n t.1 t.2‖ ≤ 2*C/r := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiOriginalEquation hp hp1 n t.1 t.2
  have ht' : t ∈ ball a (4*r) := ball_subset_ball (by linarith) ht
  have hd : DifferentiableAt ℂ F t := (hf t ht').differentiableAt (isOpen_ball.mem_nhds ht')
  have hinc : HasFDerivAt (fun b : DeletedCoeff p n => (b,t.2))
      (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) t.1 :=
    hasFDerivAt_prodMk_left t.1 t.2
  have he : sourcePsiOriginalRootJacobian hp hp1 n t.1 t.2 =
      (fderiv ℂ F t).comp (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) := by
    exact (hd.hasFDerivAt.comp t.1 hinc).fderiv
  rw [he]
  calc
    _ ≤ ‖fderiv ℂ F t‖ * ‖ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ F t‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℂ (DeletedCoeff p n) (CoeffPair p)) (norm_nonneg (fderiv ℂ F t))
    _ ≤ 2*C/r := by
      apply NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound F a t (3*r) r C hr
      · simpa only [show 3*r+r = 4*r by ring] using hf
      · simpa only [show 3*r+r = 4*r by ring] using hb
      · exact ball_subset_ball (by linarith) ht

/-- One open tube around a compact root set has the corrected joint
root/source bound, with constant 4C/r^2, uniformly in the deleted index. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_compact_complex_joint_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (K : Set (Coeff p)) (hK : IsCompact K) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ K ×ˢ {φ} ⊆ U ∧
        ∀ n : ℤ, ∀ a ∈ K, ∀ t ∈ U,
          ‖sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2 -
            sourcePsiOriginalFullRootJacobian hp hp1 n a φ‖ ≤
            (4*C/r^2)*max ‖t.1-a‖ ‖t.2-φ‖ := by
  obtain ⟨r,C,hr,hC,hb⟩ := H.originalEquation_compact_complex_ball_bound φ hφ K hK
  let U : Set (Coeff p × CoeffPair p) := ⋃ a ∈ K, ball (a,φ) r
  have hdiff (a : Coeff p) (ha : a ∈ K) (n : ℤ) : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiOriginalEquation hp hp1 n t.1 t.2)
      (ball (Coeff.deleteCoordinateTo n a,φ) (4*r)) := by
    intro v hv
    have hs : DifferentiableAt ℂ (fun v : DeletedCoeff p n × CoeffPair p => (v.2,v.1)) v :=
      differentiableAt_snd.prodMk differentiableAt_fst
    exact (((H.analytic n (v.2,v.1) ⟨(hb a ha n v hv).1,mem_univ _⟩).differentiableAt).comp v hs).differentiableWithinAt
  have hball (n : ℤ) (a : Coeff p) (t : Coeff p × CoeffPair p) (ht : t ∈ ball (a,φ) r) :
      (Coeff.deleteCoordinateTo n t.1,t.2) ∈ ball (Coeff.deleteCoordinateTo n a,φ) r := by
    rw [mem_ball,dist_eq_norm] at ht ⊢
    exact (norm_sourcePsiDeletedPair_sub_le n t (a,φ)).trans_lt ht
  have hnorm (a : Coeff p) (ha : a ∈ K) (n : ℤ)
      (t : Coeff p × CoeffPair p) (ht : t ∈ ball (a,φ) r) :
      ‖sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2‖ ≤ 2*C/r :=
    norm_sourcePsiOriginalRootJacobian_le_of_joint_ball_bound hp hp1 n
      (Coeff.deleteCoordinateTo n a,φ) r C hr
      (t := (Coeff.deleteCoordinateTo n t.1,t.2)) (hdiff a ha n)
      (fun v hv => (hb a ha n v hv).2) (hball n a t ht)
  refine ⟨r,C,hr,hC,U,isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball)),?_,?_⟩
  · rintro ⟨a,ψ⟩ ⟨ha,rfl⟩
    exact mem_iUnion₂.mpr ⟨a,ha,mem_ball_self hr⟩
  · intro n a ha t ht
    change _ ≤ (4*C/r^2)*‖t-(a,φ)‖
    let Qt := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2
    let Qa := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) φ
    have hfull : ‖sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2 -
        sourcePsiOriginalFullRootJacobian hp hp1 n a φ‖ ≤ ‖Qt-Qa‖ :=
      Coeff.norm_deletedJacobianExtension_sub_le n Qt Qa
    by_cases hnear : ‖t-(a,φ)‖ < r
    · have htball : t ∈ ball (a,φ) r := by simpa only [mem_ball,dist_eq_norm] using hnear
      have hlip := norm_sourcePsiOriginalRootJacobian_sub_le_of_joint_ball_bound hp hp1 n
        (Coeff.deleteCoordinateTo n a,φ) r C hr
        (t := (Coeff.deleteCoordinateTo n t.1,t.2)) (u := (Coeff.deleteCoordinateTo n a,φ))
        (hdiff a ha n) (fun v hv => (hb a ha n v hv).2) (hball n a t htball) (mem_ball_self hr)
      exact hfull.trans (hlip.trans (mul_le_mul_of_nonneg_left
        (norm_sourcePsiDeletedPair_sub_le n t (a,φ)) (by positivity)))
    · obtain ⟨b,hbK,htb⟩ := mem_iUnion₂.mp ht
      have hQt : ‖Qt‖ ≤ 2*C/r := hnorm b hbK n t htb
      have hQa : ‖Qa‖ ≤ 2*C/r := hnorm a ha n (a,φ) (mem_ball_self hr)
      calc
        _ ≤ ‖Qt-Qa‖ := hfull
        _ ≤ ‖Qt‖+‖Qa‖ := norm_sub_le Qt Qa
        _ ≤ 2*C/r+2*C/r := add_le_add hQt hQa
        _ = (4*C/r^2)*r := by field_simp; ring
        _ ≤ (4*C/r^2)*‖t-(a,φ)‖ := mul_le_mul_of_nonneg_left (le_of_not_gt hnear) (by positivity)

end NLS.ZakharovShabat
