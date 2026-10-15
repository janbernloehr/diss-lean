import NLS.ZakharovShabat.SourcePsiOriginalNormLimit
import NLS.SequenceSpaces.DeletedOperatorNormDifference

/-!
# Common complex charts for the actual original Jacobians

Lemma 12.4 supplies joint complex equation bounds at the deleted centers.
Coordinate decay handles the escaping indices; a finite minimum handles
the remaining ones. Cauchy estimates and norm contraction under deletion
give one joint Lipschitz bound for all original Jacobians, with both the
root and source parameters complex.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalEquation_local_bound_at_deleted_center
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (n : ℤ) (a : DeletedCoeff p n) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ t ∈ ball (a,φ) r, t.2 ∈ W ∧ ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hb⟩ := H.locally_uniform φ hφ (a:Coeff p)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU ((a:Coeff p),φ) hbase
  refine ⟨r,C,hr,hC,?_⟩
  intro t ht
  have ht' : ((t.1:Coeff p),t.2) ∈ U := hball (by simpa only [mem_ball,Prod.dist_eq,Subtype.dist_eq] using ht)
  exact ⟨(hUW ht').2,hb n t.1 t.2 ht'⟩

theorem SourceLemma12_4Data.originalEquation_tail_bound_at_deleted_centers
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (a : Coeff p) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      ∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
        t.2 ∈ W ∧ ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hb⟩ := H.locally_uniform φ hφ a
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hU (a,φ) hbase
  obtain ⟨K,hK⟩ := Coeff.exists_cutoff_norm_apply_lt hp a (half_pos hδ)
  refine ⟨δ/2,C,half_pos hδ,hC,K,?_⟩
  intro n hn t ht
  have hc : dist (Coeff.deleteCoordinate n a,φ) (a,φ) < δ/2 := by
    rw [dist_eq_norm]
    change max ‖Coeff.deleteCoordinate n a-a‖ ‖φ-φ‖ < δ/2
    simpa only [sub_self,norm_zero,Coeff.norm_deleteCoordinate_sub,max_eq_left (norm_nonneg _)] using hK n hn
  have htc : dist ((t.1:Coeff p),t.2) (Coeff.deleteCoordinate n a,φ) < δ/2 := by
    have he : ((Coeff.deleteCoordinateTo n a : DeletedCoeff p n):Coeff p) = Coeff.deleteCoordinate n a := rfl
    rw [← he]
    simpa only [mem_ball,Prod.dist_eq,Subtype.dist_eq] using ht
  have ht' : ((t.1:Coeff p),t.2) ∈ U := hball (by
    change dist ((t.1:Coeff p),t.2) (a,φ) < δ
    exact (dist_triangle _ (Coeff.deleteCoordinate n a,φ) _).trans_lt (by linarith))
  exact ⟨(hUW ht').2,hb n t.1 t.2 ht'⟩

theorem SourceLemma12_4Data.originalEquation_allIndex_complex_ball_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (a : Coeff p) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ n : ℤ,
      ∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
        t.2 ∈ W ∧ ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C := by
  classical
  obtain ⟨rt,Ct,hrt,hCt,K,htail⟩ := H.originalEquation_tail_bound_at_deleted_centers φ hφ a
  have hhead (n : ℤ) := H.originalEquation_local_bound_at_deleted_center φ hφ n (Coeff.deleteCoordinateTo n a)
  choose rh Ch hrh hCh hh using hhead
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hs : s.Nonempty := ⟨0,by simp [s]⟩
  let r := min rt (s.inf' hs rh)
  let C := max Ct (∑ n ∈ s, Ch n)
  have hr : 0 < r := lt_min hrt ((Finset.lt_inf'_iff hs).2 (fun n _ => hrh n))
  refine ⟨r,C,hr,le_max_of_le_left hCt,?_⟩
  intro n t ht
  by_cases hn : K ≤ n.natAbs
  · have h := htail n hn t (ball_subset_ball (min_le_left _ _) ht)
    exact ⟨h.1,h.2.trans (le_max_left _ _)⟩
  · have hns : n ∈ s := by
      simp only [s,Finset.mem_Icc]
      omega
    have hrn : r ≤ rh n := (min_le_right _ _).trans (Finset.inf'_le rh hns)
    have hCn : Ch n ≤ C := (Finset.single_le_sum (fun k _ => hCh k) hns).trans (le_max_right _ _)
    have h := hh n t (ball_subset_ball hrn ht)
    exact ⟨h.1,h.2.trans hCn⟩


theorem norm_sourcePsiOriginalRootJacobian_sub_le_of_joint_ball_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n × CoeffPair p) (r C : ℝ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => sourcePsiOriginalEquation hp hp1 n t.1 t.2) (ball a (4*r)))
    (hb : ∀ t ∈ ball a (4*r), ‖sourcePsiOriginalEquation hp hp1 n t.1 t.2‖ ≤ C)
    {t u : DeletedCoeff p n × CoeffPair p}
    (ht : t ∈ ball a r) (hu : u ∈ ball a r) :
    ‖sourcePsiOriginalRootJacobian hp hp1 n t.1 t.2 - sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2‖ ≤
      (4*C/r^2)*‖t-u‖ := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiOriginalEquation hp hp1 n t.1 t.2
  have hsub : ball a r ⊆ ball a (4*r) := ball_subset_ball (by linarith)
  have hd (v : DeletedCoeff p n × CoeffPair p) (hv : v ∈ ball a r) :
      DifferentiableAt ℂ F v :=
    (hf v (hsub hv)).differentiableAt (isOpen_ball.mem_nhds (hsub hv))
  have hpart (v : DeletedCoeff p n × CoeffPair p) (hv : v ∈ ball a r) :
      (fderiv ℂ F v).comp (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) =
        sourcePsiOriginalRootJacobian hp hp1 n v.1 v.2 := by
    have hinc : HasFDerivAt (fun b : DeletedCoeff p n => (b,v.2))
        (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) v.1 := hasFDerivAt_prodMk_left v.1 v.2
    exact ((hd v hv).hasFDerivAt.comp v.1 hinc).fderiv.symm
  rw [← hpart t ht,← hpart u hu,← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖fderiv ℂ F t-fderiv ℂ F u‖ * ‖ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ F t-fderiv ℂ F u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℂ (DeletedCoeff p n) (CoeffPair p)) (norm_nonneg (fderiv ℂ F t-fderiv ℂ F u))
    _ ≤ (4*C/r^2)*‖t-u‖ :=
      NLS.ComplexAnalysis.norm_fderiv_sub_le_of_holomorphic_ball_bound F a r C hr hf hb hu ht

theorem SourceLemma12_4Data.originalRootJacobian_allIndex_complex_local_Lipschitz
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (a : Coeff p) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ n : ℤ,
      ∀ t ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
        ∀ u ∈ ball (Coeff.deleteCoordinateTo n a,φ) r,
          ‖sourcePsiOriginalRootJacobian hp hp1 n t.1 t.2 - sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2‖ ≤
            L*‖t-u‖ := by
  obtain ⟨δ,C,hδ,hC,hb⟩ := H.originalEquation_allIndex_complex_ball_bound φ hφ a
  let r := δ/4
  have hr : 0 < r := by dsimp [r]; positivity
  have he : 4*r = δ := by dsimp [r]; ring
  refine ⟨r,4*C/r^2,hr,by positivity,?_⟩
  intro n t ht u hu
  apply norm_sourcePsiOriginalRootJacobian_sub_le_of_joint_ball_bound hp hp1 n
    (Coeff.deleteCoordinateTo n a,φ) r C hr ?_ ?_ ht hu
  · rw [he]
    intro v hv
    have hs : DifferentiableAt ℂ (fun v : DeletedCoeff p n × CoeffPair p => (v.2,v.1)) v :=
      differentiableAt_snd.prodMk differentiableAt_fst
    exact (((H.analytic n (v.2,v.1) ⟨(hb n v hv).1,mem_univ _⟩).differentiableAt).comp v hs).differentiableWithinAt
  · rw [he]
    exact fun v hv => (hb n v hv).2

theorem SourceLemma12_4Data.originalFullRootJacobian_complex_local_Lipschitz
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (a : Coeff p) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ n : ℤ,
      ∀ t ∈ ball (a,φ) r, ∀ u ∈ ball (a,φ) r,
        ‖sourcePsiOriginalFullRootJacobian hp hp1 n t.1 t.2 -
          sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2‖ ≤ L*‖t-u‖ := by
  obtain ⟨r,L,hr,hL,hb⟩ := H.originalRootJacobian_allIndex_complex_local_Lipschitz φ hφ a
  have hball (n : ℤ) (t : Coeff p × CoeffPair p) (ht : t ∈ ball (a,φ) r) :
      (Coeff.deleteCoordinateTo n t.1,t.2) ∈ ball (Coeff.deleteCoordinateTo n a,φ) r := by
    rw [mem_ball,dist_eq_norm] at ht ⊢
    exact (norm_sourcePsiDeletedPair_sub_le n t (a,φ)).trans_lt ht
  refine ⟨r,L,hr,hL,?_⟩
  intro n t ht u hu
  let Qt := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n t.1) t.2
  let Qu := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n u.1) u.2
  change ‖Coeff.deletedJacobianExtension n Qt-Coeff.deletedJacobianExtension n Qu‖ ≤ L*‖t-u‖
  calc
    _ ≤ ‖Qt-Qu‖ := Coeff.norm_deletedJacobianExtension_sub_le n Qt Qu
    _ ≤ L*‖(Coeff.deleteCoordinateTo n t.1,t.2)-(Coeff.deleteCoordinateTo n u.1,u.2)‖ :=
      hb n (Coeff.deleteCoordinateTo n t.1,t.2) (hball n t ht)
        (Coeff.deleteCoordinateTo n u.1,u.2) (hball n u hu)
    _ ≤ L*‖t-u‖ := mul_le_mul_of_nonneg_left (norm_sourcePsiDeletedPair_sub_le n t u) hL

end NLS.ZakharovShabat
