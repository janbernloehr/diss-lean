import NLS.ZakharovShabat.SourceRenormalizedImageTrajectories

/-! # Constructed local and small-data analytic renormalized dynamics

This supplies the spectral-flow part of Corollary 22.2(ii): a local
analytic trajectory map around every real source and global analytic
trajectories on an invariant neighborhood of zero. The data are the
constructed moment atlas and actual Birkhoff family, at every finite
exponent above one. Agreement with classical PDE solutions is separate.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₀ B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every source has a neighborhood with a common positive time interval and analytic trajectories. -/
theorem exists_local_analytic_renormalizedTrajectories (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (φ : realTypeSourceSubmodule p) :
    ∃ T > 0, ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ φ ∈ V ∧
      V ⊆ A.renormalizedTrajectoryDomain t T ∧ AnalyticOnNhd ℝ (A.renormalizedImageTrajectoryOn D T) V := by
  obtain ⟨T,hT,V,hV,hφ,hvalid⟩ := A.exists_local_renormalizedImageFlow hs hP hr D φ
  have hsub : V ⊆ A.renormalizedTrajectoryDomain t T := fun ψ hψ τ => hvalid ψ hψ τ.val τ.property
  exact ⟨T,hT,V,hV,hφ,hsub,(A.analytic_renormalizedImageTrajectoryOn hs hP hr D T).mono hsub⟩

/-- One invariant open source neighborhood admits analytic trajectories on every compact interval. -/
theorem exists_small_global_analytic_renormalizedTrajectories
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) :
    ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ (0 : realTypeSourceSubmodule p) ∈ V ∧
      (∃ r > 0, Metric.ball 0 r ⊆ V) ∧
      (∀ φ ∈ V, ∀ τ : ℝ, (τ,φ) ∈ A.renormalizedImageDomain t) ∧
      (∀ φ ∈ V, ∀ τ : ℝ, A.renormalizedImageFlow D φ τ ∈ V) ∧
      (∀ T : ℝ, AnalyticOnNhd ℝ (A.renormalizedImageTrajectoryOn D T) V) ∧
      ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedImageFlow D x.2 x.1)
        (univ ×ˢ V) ∧
      ∀ φ ∈ V, ∀ τ σ : ℝ,
        A.renormalizedImageFlow D (A.renormalizedImageFlow D φ σ) τ =
          A.renormalizedImageFlow D φ (τ+σ) := by
  obtain ⟨V,hV,hzero,hball,hvalid,hinv⟩ := A.exists_invariant_small_renormalizedFlow D
  refine ⟨V,hV,hzero,hball,hvalid,hinv,?_,?_,?_⟩
  · intro T
    exact (A.analytic_renormalizedImageTrajectoryOn hs hP hr D T).mono (fun φ hφ τ => hvalid φ hφ τ.val)
  · exact (A.continuousOn_renormalizedImageFlow hs hP hr D).mono (fun x hx => hvalid x.2 hx.2 x.1)
  · intro φ hφ τ σ
    exact A.renormalizedImageFlow_add hs.toSourcePsiIsolatingComplexExtension D φ τ σ (hvalid φ hφ σ)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Local and small-data global analytic spectral flows, built from the actual spectral objects. -/
theorem exists_local_and_small_global_renormalizedFlow (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
      (∀ φ : realTypeSourceSubmodule p,
        ∃ T > 0, ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ φ ∈ V ∧
          V ⊆ A.renormalizedTrajectoryDomain t T ∧
          AnalyticOnNhd ℝ (A.renormalizedImageTrajectoryOn D T) V) ∧
      (∀ φ τ, (τ,φ) ∈ A.renormalizedImageDomain t →
        sourceComplexBirkhoffMap hp hp1 t (A.renormalizedImageFlow D φ τ).val =
          A.renormalizedPhaseTrajectory t φ τ) ∧
      (∀ φ τ, (τ,φ) ∈ A.renormalizedImageDomain t → ∀ n,
        sourceComplexAction hp hp1 n (A.renormalizedImageFlow D φ τ).val =
          sourceComplexAction hp hp1 n φ.val) ∧
      ∃ V : Set (realTypeSourceSubmodule p), IsOpen V ∧ (0 : realTypeSourceSubmodule p) ∈ V ∧
        (∃ r > 0, Metric.ball 0 r ⊆ V) ∧
        (∀ φ ∈ V, ∀ τ : ℝ, (τ,φ) ∈ A.renormalizedImageDomain t) ∧
        (∀ φ ∈ V, ∀ τ : ℝ, A.renormalizedImageFlow D φ τ ∈ V) ∧
        (∀ T : ℝ, AnalyticOnNhd ℝ (A.renormalizedImageTrajectoryOn D T) V) ∧
        ContinuousOn (fun x : ℝ × realTypeSourceSubmodule p => A.renormalizedImageFlow D x.2 x.1)
          (univ ×ˢ V) ∧
        ∀ φ ∈ V, ∀ τ σ : ℝ,
          A.renormalizedImageFlow D (A.renormalizedImageFlow D φ σ) τ =
            A.renormalizedImageFlow D φ (τ+σ) := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W,s,A,W₀,B,X,t,D,A.exists_local_analytic_renormalizedTrajectories hs hP hr D,
    A.complex_map_renormalizedImageFlow D,A.renormalizedImageFlow_action D,
    A.exists_small_global_analytic_renormalizedTrajectories hs hP hr D⟩

end NLS.ZakharovShabat
