import NLS.ZakharovShabat.SourceAngularOriginalBetaValues
import NLS.ZakharovShabat.SourceAngularBetaCauchyAnalytic
import NLS.ZakharovShabat.SourceAngularBetaLocalBound
import NLS.ZakharovShabat.SourcePeriodicSegmentComplexStability

/-!
# Beta analyticity throughout the original complex domain

Original isolating disks supply annular primitives near every complex
source. Stability of the whole periodic segment avoids any assumption
that the ordered endpoints are analytic. Cauchy reconstruction includes
collapsed gaps and periodic terminals without dividing by the gap.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every complex source has a chart inside its original isolating disk family. -/
theorem angular_original_annulus_chart (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (m : ℤ) :
    ∃ V : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ,
      ∃ r R : ℝ, ∃ z₀ : ℂ, φ ∈ V ∧
        SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀ ∧
        ∃ C : ℝ, SourceIsolatingNeighborhoods hp hp1 V (fun k => ball (c k) (T k)) C := by
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  let H2 := H.previous.previous.psi.previous.quotients.roots.roots.symmetric
  have H15 : SourceEquation2_15Data hp hp1 W₀ :=
    H.previous.previous.psi.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous
  obtain ⟨U,hU,hφU,hUW,D,C,hD,hterm⟩ := H.angular_original_disks φ hφ
  choose a T hT he using hD.discs
  let c : ℤ → ℂ := fun k => (a k:ℂ)
  have hdiscs (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      SourceAngularDirichletDiscFamilyData hp hp1 s ψ c T := by
    let P := fun k => hD.periodCircle ψ hψ k (a k) (T k) (hT k) (he k)
    refine ⟨⟨fun _ => rfl,fun k => ⟨hT k,(P k).gap,(P k).closedBall_subset_omittedDomain,
      (P k).sphere_subset_rootDomain⟩⟩,?_,?_⟩
    · intro k
      change sourceSpectralCluster hp hp1 ψ k ⊆ ball (a k:ℂ) (T k)
      rw [← he k]
      exact hD.cluster ψ hψ k
    · intro n k
      exact H.previous.previous.psi.period ψ (hUW hψ) n k (P k)
  have hgeom := (hdiscs φ hφU).contour_family.2 m
  obtain ⟨r₀,R₀,hr₀,hr₀R₀,hR₀T,hseg₀⟩ := exists_nested_radii_of_segment_subset_ball _ _
    (c m) (T m) hgeom.2.1
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m
  let q := max r₀ (dist μ (c m))
  have hqT : q < T m := max_lt (hr₀R₀.trans hR₀T) ((hdiscs φ hφU).dirichlet_mem_ball m)
  have hq : 0 < q := hr₀.trans_le (le_max_left _ _)
  let r := (2*q+T m)/3
  let R := (q+2*T m)/3
  have hqr : q < r := by dsimp [r]; linarith
  have hr : 0 < r := hq.trans hqr
  have hrR : r < R := by dsimp [r,R]; linarith
  have hRT : R < T m := by dsimp [R]; linarith
  have hsegr : sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) r :=
    hseg₀.trans (ball_subset_ball ((le_max_left _ _).trans hqr.le))
  have hμr : μ ∈ ball (c m) r := lt_of_le_of_lt (le_max_right _ _) hqr
  have hsphere := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m (c m) r hsegr
    ((closedBall_subset_closedBall (hrR.trans hRT).le).trans hgeom.2.2.1)
  have hgap := H15.eventually_gap_subset_ball φ (H.previous.previous.subset hφ) m (c m) r hsegr hsphere
  have hμ : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) r :=
    (H2.simplicity.boundary φ (H.previous.previous.subset hφ) .dirichlet m).1.continuousAt.eventually
      (isOpen_ball.mem_nhds hμr)
  obtain ⟨O,hOsub,hO,hφO⟩ := _root_.mem_nhds_iff.mp (hgap.and hμ)
  let V := U ∩ O
  have hV : IsOpen V := hU.inter hO
  have hVW : V ⊆ W := inter_subset_left.trans hUW
  let z₀ : ℂ := c m+((r+R)/2:ℝ)
  have hz₀ : z₀ ∈ ball (c m) R \ closedBall (c m) r := by
    have hd : dist z₀ (c m) = (r+R)/2 := by
      simp only [z₀,dist_eq_norm,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
    exact ⟨mem_ball.mpr (by rw [hd]; linarith),
      fun h => by have hh := mem_closedBall.mp h; rw [hd] at hh; linarith⟩
  have hfamily : (fun k => ball (c k) (T k)) = D := by
    funext k
    exact (he k).symm
  refine ⟨V,c,T,r,R,z₀,⟨hφU,hφO⟩,?_,C,?_⟩
  · exact H.angular_extension.toSourcePsiIsolatingComplexExtension.joint_angular_annulus_chart_of_geometry
      W hW (Subset.refl _) (fun ψ hψ k =>
        ⟨H2.midpoint k ψ (H.previous.previous.subset hψ),H2.squared_gap k ψ (H.previous.previous.subset hψ)⟩)
      V hV hVW m c T r R z₀ hr hrR hRT hz₀ (fun ψ hψ => hdiscs ψ hψ.1)
      (fun ψ hψ => (hOsub hψ.2).1) (fun ψ hψ => (hOsub hψ.2).2)

  · rw [hfamily]
    exact hD.restrict_source inter_subset_left

/-- Each off-diagonal beta is complex analytic on the unchanged W. -/
theorem beta_original_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (n m : ℤ) (hmn : m ≠ n) : AnalyticOnNhd ℂ (sourceAngularBeta hp hp1 n m s) W := by
  intro φ hφ
  obtain ⟨V,c,T,r,R,z₀,hφV,D,_⟩ := H.angular_original_annulus_chart φ hφ m
  exact D.analyticAt_beta n hmn φ hφV
    (H.previous.previous.psi.previous.quotients.roots.roots.symmetric.simplicity.boundary φ
      (H.previous.previous.subset hφ) .dirichlet m).1

/-- The original beta has a local gap-weight bound for each fixed pair. -/
theorem beta_original_local_gap_weight_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n m : ℤ) (hmn : m ≠ n) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ V,
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-sourceStandardRootMidpoint hp hp1 ψ m‖) := by
  obtain ⟨U,c,T,r,R,z₀,hφU,D,_⟩ := H.angular_original_annulus_chart φ hφ m
  obtain ⟨V,hV,hφV,hVU,C,hC,hb⟩ := D.exists_local_norm_beta_le_gap_weight φ hφU n hmn
  exact ⟨V,hV,hφV,hVU.trans D.source_subset,C,hC,hb⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
