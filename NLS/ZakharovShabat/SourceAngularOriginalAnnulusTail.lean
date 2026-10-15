import NLS.ZakharovShabat.SourceAngularOriginalAnnulus
import NLS.ZakharovShabat.SourceAngularUniformAnnulusPrimitive

/-!
# Fixed angular annuli at every complex source

The retained domain makes every scalar boundary root analytic. Sequence
norm analyticity then controls the Dirichlet tail near any complex
source. Together with the original quarter-pi tail disks, this supplies
fixed annular charts for all sufficiently distant selected indices.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual boundary displacement sequences are analytic on the retained W. -/
theorem boundary_original_displacement_analytic (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (b : BoundaryCondition) : AnalyticOnNhd ℂ (sourceBoundaryDisplacement hp hp1 b) W := by
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  apply analyticOnNhd_sourceBoundaryDisplacement_of_roots hp hp1 W hW
  intro b m ψ hψ
  exact (H.previous.previous.psi.previous.quotients.roots.roots.symmetric.simplicity.boundary ψ
    (H.previous.previous.subset hψ) b m).1

/-- One fixed annulus geometry works for every sufficiently distant index. -/
theorem angular_original_annulus_tail (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ T : ℤ → ℝ, ∀ m : ℤ, K < m.natAbs →
        c m = (Real.pi:ℂ)*m ∧ T m = Real.pi/4 ∧
          SourceAngularJointAnnulusChartData hp hp1 m s W V c T
            (Real.pi/16) (Real.pi/8) (c m+(3*Real.pi/32:ℝ)) := by
  classical
  have hW : IsOpen W := by
    obtain ⟨A,hW,_⟩ := H.previous.previous.atlas
    exact hW ▸ A.toSourcePsiComplexRootAtlas.isOpen_domain
  let H2 := H.previous.previous.psi.previous.quotients.roots.roots.symmetric
  have hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ :=
    fun ψ hψ k => ⟨H2.midpoint k ψ (H.previous.previous.subset hψ),
      H2.squared_gap k ψ (H.previous.previous.subset hψ)⟩
  obtain ⟨U,hU,hφU,hUW,D,C,hD,_⟩ := H.angular_original_disks φ hφ
  choose a₀ T₀ hT₀ he₀ using hD.discs
  obtain ⟨N,htail⟩ := hD.tail
  let a : ℤ → ℝ := fun k => if N < k.natAbs then Real.pi*k else a₀ k
  let c : ℤ → ℂ := fun k => (a k:ℂ)
  let T : ℤ → ℝ := fun k => if N < k.natAbs then Real.pi/4 else T₀ k
  have hT (k : ℤ) : 0 < T k := by
    dsimp only [T]
    split_ifs
    · positivity
    · exact hT₀ k
  have he (k : ℤ) : D k = ball (a k:ℂ) (T k) := by
    by_cases hk : N < k.natAbs
    · simpa [a,T,hk,refinedResonantDisk,Complex.ofReal_mul] using htail k hk
    · simpa [a,T,hk] using he₀ k
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
  obtain ⟨Kg,Vg,hVg,hφg,hgap⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨Kμ,Vμ,hVμ,hφμ,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates hp
    (sourceBoundaryDisplacement hp hp1 .dirichlet) φ
    (H.boundary_original_displacement_analytic .dirichlet φ hφ).continuousAt
    (Real.pi/16) (by positivity)
  have hterminal (ψ : CoeffPair p) (hψ : ψ ∈ Vμ) (m : ℤ) (hm : Kμ < m.natAbs) :
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball ((Real.pi:ℂ)*m) (Real.pi/16) := by
    simpa only [mem_ball,dist_eq_norm,sourceBoundaryDisplacement_apply] using hsmall ψ hψ m hm
  let K := max N (max Kg Kμ)
  let V := (U ∩ Vg) ∩ Vμ
  have hV : IsOpen V := (hU.inter hVg).inter hVμ
  have hVW : V ⊆ W := fun ψ hψ => hUW hψ.1.1
  refine ⟨V,hV,⟨⟨hφU,hφg⟩,hφμ⟩,hVW,K,c,T,?_⟩
  intro m hmK
  have hmN : N < m.natAbs := (le_max_left _ _).trans_lt hmK
  have hmKg : Kg ≤ m.natAbs := by dsimp only [K] at hmK; omega
  have hmKμ : Kμ < m.natAbs := by dsimp only [K] at hmK; omega
  have hc : c m = (Real.pi:ℂ)*m := by simp [c,a,hmN,Complex.ofReal_mul]
  have hT : T m = Real.pi/4 := by simp [T,hmN]
  have hr : 0 < Real.pi/16 := by positivity
  have hrR : Real.pi/16 < Real.pi/8 := by nlinarith [Real.pi_pos]
  have hRT : Real.pi/8 < T m := by rw [hT]; nlinarith [Real.pi_pos]
  have hz₀ : c m+(3*Real.pi/32:ℝ) ∈ ball (c m) (Real.pi/8) \ closedBall (c m) (Real.pi/16) := by
    have hdist : dist (c m+(3*Real.pi/32:ℝ)) (c m) = 3*Real.pi/32 := by
      simp only [dist_eq_norm,add_sub_cancel_left,Complex.norm_real]
      exact Real.norm_of_nonneg (by positivity)
    exact ⟨mem_ball.mpr (by rw [hdist]; nlinarith [Real.pi_pos]),
      fun h => by have hle := mem_closedBall.mp h; rw [hdist] at hle; nlinarith [Real.pi_pos]⟩
  have hg (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (Real.pi/16) := by
    rw [hc]
    obtain ⟨hmid,hgapSmall⟩ := hgap ψ hψ.1.2 m hmKg
    apply sourcePeriodicSegment_subset_ball_of_midpoint_gap_bound
    nlinarith [Real.pi_pos]
  have ht (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (c m) (Real.pi/16) := by
    rw [hc]
    exact hterminal ψ hψ.2 m hmKμ
  exact ⟨hc,hT,H.angular_extension.toSourcePsiIsolatingComplexExtension.joint_angular_annulus_chart_of_geometry W hW (Subset.refl _) hA V hV hVW
    m c T _ _ _ hr hrR hRT hz₀ (fun ψ hψ => hdiscs ψ hψ.1.1) hg ht⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
