import NLS.ZakharovShabat.SourceDeletedPairJointAnalytic
import NLS.ZakharovShabat.SourceLemma10_5
import NLS.ComplexAnalysis.CompactParameterBounds

/-! # The full joint domain of the deleted pair product in F.1

The omitted-root square gives analyticity near the selected endpoints.
Away from them the exact discriminant factorization gives an analytic
quotient. Together these cover the whole spectral plane without shrinking
the original source domain.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The literal deleted pair product is jointly analytic on the full spectral/source product. -/
theorem SourceLemma10_5Data.deletedPair_joint_full
    (H : SourceLemma10_5Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceDeletedPairJointProduct hp hp1 n) (univ ×ˢ W) := by
  intro q hq
  by_cases hz : q.1 ∈ sourceStandardRootOmittedDomain hp hp1 q.2 n
  · exact sourceDeletedPairJointProduct_analyticOnNhd_of_omitted hp hp1 W n
      (H.joint n).1 (H.joint n).2 q ⟨hq.2,hz⟩
  let A := fun t : ℂ × CoeffPair p =>
    (canonicalPeriodicLeft hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n-t.1)*
      (canonicalPeriodicRight hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n-t.1)
  have hA : AnalyticAt ℂ A q := H.roots.symmetric.joint_factor n q hq
  have hne : A q ≠ 0 := by
    obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.neighborhoods q.2 hq.2
    have hseg : sourcePeriodicSegment hp hp1 q.2 n ⊆
        sourceStandardRootOmittedDomain hp hp1 q.2 n :=
      (hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain q.2 hψV n).trans'
        (hD.gap q.2 hψV n)
    apply mul_ne_zero
    · intro he
      apply hz
      rw [← sub_eq_zero.mp he]
      exact hseg (left_mem_segment ℝ _ _)
    · intro he
      apply hz
      rw [← sub_eq_zero.mp he]
      exact hseg (right_mem_segment ℝ _ _)
  have hden : AnalyticAt ℂ (fun t => (-4:ℂ)*A t) q := analyticAt_const.mul hA
  have hden0 : (-4:ℂ)*A q ≠ 0 := mul_ne_zero (by norm_num) hne
  have hnum : AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
      (canonicalDiscriminant hp (periodOnePotential t.2) t.1)^2-4) q :=
    ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 q
      (mem_univ q)).pow 2).sub analyticAt_const
  apply (hnum.div hden hden0).congr
  filter_upwards [hden.continuousAt.eventually_ne hden0] with t ht
  have hfac := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1
    (periodOnePotential t.2) (periodOnePotential_mem t.2) n t.1
  change (_-4)/((-4:ℂ)*A t) = sourceDeletedPairJointProduct hp hp1 n t
  rw [hfac]
  rw [mul_assoc (-4:ℂ)]
  exact mul_div_cancel_left₀ _ ht

/-- The spectral derivative is jointly analytic on the same full domain. -/
theorem SourceLemma10_5Data.deletedPair_derivative_joint_full
    (H : SourceLemma10_5Data hp hp1 W) (hW : IsOpen W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      deriv (canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential t.2) (periodOnePotential_mem t.2) n) t.1) (univ ×ˢ W) := by
  let P := sourceDeletedPairJointProduct hp hp1 n
  let ev : ((ℂ × CoeffPair p) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1,0)
  have hP := H.deletedPair_joint_full n
  have hd := ev.comp_analyticOnNhd hP.fderiv
  apply hd.congr (isOpen_univ.prod hW)
  intro t ht
  exact (NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv P t.1 t.2
    (hP t ht).differentiableAt).symm

/-- The zeros are exactly the actual endpoints with an index different from the deleted pair. -/
theorem SourceLemma10_5Data.deletedPair_eq_zero_iff
    (H : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (z : ℂ) :
    canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n z = 0 ↔
      ∃ m : ℤ, m ≠ n ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = z ∨
          canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = z) := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.neighborhoods ψ hψ
  have hend (m : ℤ)
      (hm : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = z ∨
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = z) :
      z ∈ D m := by
    apply hD.gap ψ hψV m
    rcases hm with h | h
    · rw [← h]; exact left_mem_segment ℝ _ _
    · rw [← h]; exact right_mem_segment ℝ _ _
  have hfac := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n z
  constructor
  · intro hzero
    have hΔ : (canonicalDiscriminant hp (periodOnePotential ψ) z)^2 = 4 := by
      rw [hzero,mul_zero] at hfac
      exact sub_eq_zero.mp hfac
    obtain ⟨m,hm⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1 _ (periodOnePotential_mem ψ) z).mp
      ((canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem ψ) z).mp hΔ)
    refine ⟨m,?_,hm⟩
    intro he
    subst m
    exact canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain hp hp1 ψ n z
      (hD.toSourceIsolatingNeighborhoods.disk_subset_omittedDomain ψ hψV n (hend n hm)) hzero
  · rintro ⟨m,hmn,hm⟩
    have hΔ := (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem ψ) z).mpr
      ((canonicalPeriodicEndpoints_exhaustive hp hp1 _ (periodOnePotential_mem ψ) z).mpr ⟨m,hm⟩)
    have hnot : z ∉ D n := fun hz =>
      Set.disjoint_left.mp (hD.disjoint n m hmn.symm) hz (hend m hm)
    have hl : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z ≠ 0 :=
      fun h => hnot (hend n (Or.inl (sub_eq_zero.mp h)))
    have hr : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z ≠ 0 :=
      fun h => hnot (hend n (Or.inr (sub_eq_zero.mp h)))
    rw [hΔ,sub_self] at hfac
    exact (mul_eq_zero.mp hfac.symm).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) hl) hr)

/-- The closure of the original isolating disc still avoids every other actual gap. -/
theorem SourceIsolatingNeighborhoods.closedDisk_subset_omittedDomain
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    closure (D n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  intro z hz m hmn hseg
  obtain ⟨a,r,_,he⟩ := hD.discs m
  have hopen : IsOpen (D m) := by rw [he]; exact Metric.isOpen_ball
  exact Set.disjoint_left.mp ((hD.disjoint n m hmn.symm).closure_left hopen)
    hz (hD.gap ψ hψ m hseg)

/-- One source neighborhood supplies positive lower and derivative upper bounds on the whole original disc. -/
theorem SourceLemma10_5Data.deletedPair_uniform_disk_bounds
    (H : SourceLemma10_5Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ ∀ ψ ∈ U, ∀ z ∈ closure (D n),
        s ≤ ‖canonicalDeletedPeriodicProduct hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n z‖ ∧
        ‖deriv (canonicalDeletedPeriodicProduct hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n) z‖ ≤ r := by
  let P := sourceDeletedPairJointProduct hp hp1 n
  let O := sourceStandardRootOmittedJointDomain hp hp1 W n
  have hK : IsCompact (closure (D n)) := by
    obtain ⟨a,r,hr,he⟩ := hD.discs n
    rw [he,closure_ball _ hr.ne']
    exact isCompact_closedBall _ _
  have hPA : AnalyticOnNhd ℂ P O :=
    sourceDeletedPairJointProduct_analyticOnNhd_of_omitted hp hp1 W n (H.joint n).1 (H.joint n).2
  have hPne : ∀ q ∈ O, P q ≠ 0 := fun q hq =>
    canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain hp hp1 q.2 n q.1 hq.2
  have hInv : ContinuousOn (fun q => (P q)⁻¹) O := hPA.continuousOn.inv₀ hPne
  obtain ⟨U₁,hU₁,hφ₁,B,hB,hb⟩ :=
    NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
      (fun q => (P q)⁻¹) O (H.joint n).1 hInv (closure (D n)) hK φ
      (fun z hz => ⟨hVW hφ,hD.closedDisk_subset_omittedDomain φ hφ n hz⟩)
  obtain ⟨U₂,hU₂,hφ₂,R,hR,hr⟩ :=
    NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
      (fun q : ℂ × CoeffPair p => deriv (canonicalDeletedPeriodicProduct hp hp1
        (periodOnePotential q.2) (periodOnePotential_mem q.2) n) q.1)
      (univ ×ˢ W) (isOpen_univ.prod hW) (H.deletedPair_derivative_joint_full hW n).continuousOn
      (closure (D n)) hK φ (fun z _ => ⟨mem_univ z,hVW hφ⟩)
  refine ⟨U₁ ∩ U₂ ∩ V,(hU₁.inter hU₂).inter hV,⟨⟨hφ₁,hφ₂⟩,hφ⟩,
    inter_subset_right,(B+1)⁻¹,R+1,by positivity,by positivity,?_⟩
  intro ψ hψ z hz
  have hbz := hb ψ hψ.1.1 z hz
  have hn : 0 < ‖P (z,ψ)‖ := norm_pos_iff.mpr (hPne (z,ψ) hbz.1)
  have hinv : ‖P (z,ψ)‖⁻¹ ≤ B := by simpa only [norm_inv] using hbz.2
  constructor
  · change (B+1)⁻¹ ≤ ‖P (z,ψ)‖
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < B+1)).mpr
    rw [inv_eq_one_div] at hinv
    have hm := (div_le_iff₀ hn).mp hinv
    nlinarith
  · exact (hr ψ hψ.1.2 z hz).2.trans (by linarith)

/-- At a collapsed gap the same disc bounds can be retained while imposing the source smallness condition. -/
theorem SourceLemma10_5Data.deletedPair_collapsed_disk_bounds
    (H : SourceLemma10_5Data hp hp1 W) (hW : IsOpen W)
    {V : Set (CoeffPair p)} (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ s r : ℝ, 0 < s ∧ 0 < r ∧ ∀ ψ ∈ U,
        ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖*r ≤ s ∧
        ∀ z ∈ closure (D n),
          s ≤ ‖canonicalDeletedPeriodicProduct hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) n z‖ ∧
          ‖deriv (canonicalDeletedPeriodicProduct hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) n) z‖ ≤ r := by
  obtain ⟨U,hU,hφU,hUV,s,r,hs,hr,hb⟩ := H.deletedPair_uniform_disk_bounds hW hV hVW hD φ hφ n
  have hg : ContinuousAt (fun ψ : CoeffPair p =>
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖) φ := by
    simpa only [norm_pow,Real.sqrt_sq (norm_nonneg _)] using
      (H.roots.symmetric.squared_gap n φ (hVW hφ)).continuousAt.norm.sqrt
  have hsmall : ∀ᶠ ψ in 𝓝 φ,
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖*r < s :=
    (hg.mul continuousAt_const).eventually (gt_mem_nhds (by
      change ‖canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n‖*r < s
      rw [hgap,norm_zero,zero_mul]
      exact hs))
  obtain ⟨T,hTsub,hT,hφT⟩ := _root_.mem_nhds_iff.mp (hsmall.and (hU.mem_nhds hφU))
  exact ⟨T,hT,hφT,fun ψ hψ => hUV (hTsub hψ).2,s,r,hs,hr,
    fun ψ hψ => ⟨(hTsub hψ).1.le,hb ψ (hTsub hψ).2⟩⟩

end NLS.ZakharovShabat
