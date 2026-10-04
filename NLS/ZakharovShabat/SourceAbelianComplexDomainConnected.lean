import NLS.ZakharovShabat.SourceAbelianUniformRealNormalization
import NLS.ComplexAnalysis.RealCenteredDiscExterior

/-! # Connectedness for complex-source spectral cut complements

The uniformly bounded real-centered isolating discs have a connected
exterior. Each moving complex cut disc is connected and meets that
exterior on a nonempty collar. Their union is the complete cut
complement, including at complex potentials.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}

theorem exterior_eq (D : SourceAbelianUniformDiscFamily hp hp1 W) :
    D.exterior = realCenteredDiscExterior D.center D.inner := by
  ext z
  simp only [exterior,realCenteredDiscExterior,mem_compl_iff,mem_iUnion,not_exists,mem_closedBall,not_le,mem_ofPred_eq]

theorem isPathConnected_exterior (D : SourceAbelianUniformDiscFamily hp hp1 W) : IsPathConnected D.exterior := by
  obtain ⟨B,hB⟩ := D.outer_bounded
  obtain ⟨a,ha,haReal⟩ := D.exists_real_mem_exterior
  rw [D.exterior_eq] at ha ⊢
  exact isPathConnected_realCenteredDiscExterior D.center D.inner D.center_real B
    (fun j => (D.inner_lt j).le.trans (hB j)) a ha haReal

/-- Two source-ball constructions share an open exterior region,
regardless of their real anchors or assigned discs. -/
theorem exterior_inter_nonempty (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (E : SourceAbelianUniformDiscFamily hp hp1 V) : (D.exterior ∩ E.exterior).Nonempty := by
  obtain ⟨B,hB⟩ := D.outer_bounded
  obtain ⟨C,hC⟩ := E.outer_bounded
  let a : ℂ := I*(max B C+1:ℝ)
  have hi : a.im = max B C+1 := by simp [a]
  have hBa : B < |a.im| := by rw [hi]; exact ((le_max_left B C).trans_lt (lt_add_one _)).trans_le (le_abs_self _)
  have hCa : C < |a.im| := by rw [hi]; exact ((le_max_right B C).trans_lt (lt_add_one _)).trans_le (le_abs_self _)
  rw [D.exterior_eq,E.exterior_eq]
  exact ⟨a,mem_discExterior_of_abs_im_gt _ _ D.center_real B (fun j => (D.inner_lt j).le.trans (hB j)) a hBa,
    mem_discExterior_of_abs_im_gt _ _ E.center_real C (fun j => (E.inner_lt j).le.trans (hC j)) a hCa⟩

theorem collar_nonempty (D : SourceAbelianUniformDiscFamily hp hp1 W) (j : ℤ) :
    (ball (D.center j) (D.outer j) \ closedBall (D.center j) (D.inner j)).Nonempty := by
  let r := (D.inner j+D.outer j)/2
  have hr : 0 < r := by dsimp [r]; linarith [D.inner_pos j,D.inner_lt j]
  have he : dist (D.center j+(r:ℂ)) (D.center j) = r := by
    simp only [dist_eq_norm,add_sub_cancel_left,norm_real,Real.norm_eq_abs,abs_of_pos hr]
  refine ⟨D.center j+(r:ℂ),?_,?_⟩
  · rw [mem_ball,he]; dsimp [r]; linarith [D.inner_lt j]
  · rw [mem_closedBall,he]; dsimp [r]; linarith [D.inner_lt j]

/-- The full complement of the moving complex cuts is connected at
all sources covered by a uniform disc family. -/
theorem isConnected_rootDomain (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) :
    IsConnected (sourceCanonicalRootDomain hp hp1 ψ) := by
  let U : ℤ → Set ℂ := fun j => ball (D.center j) (D.outer j) \ sourcePeriodicSegment hp hp1 ψ j
  have hE := D.isPathConnected_exterior.isConnected
  have hU (j : ℤ) : IsConnected (U j) :=
    isConnected_sourceAbelian_complexDisc hp hp1 ψ j (D.center j) (D.outer j)
      ((D.segment_subset ψ hψ j).trans (ball_subset_ball (D.inner_lt j).le))
  have hmeet (j : ℤ) : (D.exterior ∩ U j).Nonempty := by
    obtain ⟨a,ha⟩ := D.collar_nonempty j
    exact ⟨a,D.collar_subset_exterior j ha,ha.1,fun hs => ha.2 (ball_subset_closedBall (D.segment_subset ψ hψ j hs))⟩
  have hfamily (j : ℤ) : IsConnected (D.exterior ∪ U j) := hE.union (hmeet j) (hU j)
  obtain ⟨a,ha⟩ := hE.nonempty
  have hcommon : (⋂ j, D.exterior ∪ U j).Nonempty := ⟨a,mem_iInter.mpr (fun _ => Or.inl ha)⟩
  have hpre := isPreconnected_iUnion hcommon (fun j => (hfamily j).isPreconnected)
  have heq : (⋃ j, D.exterior ∪ U j) = D.exterior ∪ ⋃ j, U j := by
    ext z
    simp only [mem_iUnion,mem_union]
    constructor
    · rintro ⟨j,hj | hj⟩
      · exact Or.inl hj
      · exact Or.inr ⟨j,hj⟩
    · rintro (hz | ⟨j,hj⟩)
      · exact ⟨0,Or.inl hz⟩
      · exact ⟨j,Or.inr hj⟩
  rw [heq] at hpre
  rw [D.rootDomain_eq_union ψ hψ]
  exact ⟨⟨a,Or.inl ha⟩,hpre⟩

/-- The complex spectral domain remains open when collapsed gaps
are filled, with no finite-gap assumption. -/
theorem isOpen_openGapComplement (D : SourceAbelianUniformDiscFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball D.source.val D.sourceRadius) :
    IsOpen (sourceOpenGapComplement hp hp1 ψ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases mem_sourceOpenGapComplement_cases hp hp1 ψ z hz with hroot | ⟨j,hj,hseg⟩
  · exact mem_of_superset ((D.isOpen_rootDomain ψ hψ).mem_nhds hroot)
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ)
  · have hzB : z ∈ ball (D.center j) (D.outer j) :=
      (ball_subset_ball (D.inner_lt j).le) (D.segment_subset ψ hψ j hseg)
    apply mem_of_superset (isOpen_ball.mem_nhds hzB)
    intro w hw k hk
    have hkj : k ≠ j := by rintro rfl; exact hk hj
    exact D.avoids_other ψ hψ j (ball_subset_closedBall hw) k hkj

end NLS.ZakharovShabat.SourceAbelianUniformDiscFamily
