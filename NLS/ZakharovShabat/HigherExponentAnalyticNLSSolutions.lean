import NLS.ZakharovShabat.GlobalAnalyticNLSSolutions
import NLS.ZakharovShabat.SourceRenormalizedLocalExistence

/-! # Local and small-data global analytic renormalized solutions

The constructed image-domain neighborhoods supply actual solutions in the
all-smooth-sequence sense, with analytic dependence in the compact trajectory
norm. No image-domain or spectral-atlas premise is left to the user.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- On an all-time admissible set, the image flow is a global approximation solution. -/
theorem renormalizedImageFlow_isGlobalSolution
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (h2p : 2 ≤ p) (U : Set (realTypeSourceSubmodule p))
    (hvalid : ∀ φ ∈ U, ∀ time : ℝ, (time,φ) ∈ A.renormalizedImageDomain t)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ U) :
    IsRenormalizedNLSSolutionOn univ φ (A.hamiltonianRenormalizedImageFlow D φ) := by
  refine ⟨mem_univ _,?_,A.hamiltonianRenormalizedImageFlow_zero D φ,?_⟩
  · have hg : Continuous (fun time : ℝ => (time,φ)) := continuous_id.prodMk continuous_const
    have hm : MapsTo (fun time : ℝ => (time,φ)) univ (univ ×ˢ U) :=
      fun _ _ => ⟨mem_univ _,hφ⟩
    have hc := (A.continuousOn_hamiltonianRenormalizedImageFlow hs hP hr D U hvalid).comp
      (s := univ) hg.continuousOn hm
    change ContinuousOn (A.hamiltonianRenormalizedImageFlow D φ) univ at hc
    exact hc
  · intro f hf time _
    have hadm : φ ∈ A.renormalizedTrajectoryDomain t |time| := fun τ => hvalid φ hφ τ.val
    exact (A.tendstoUniformlyOn_constructedRenormalizedImageSource hs hP hr D h2p f φ hf |time| hadm).tendsto_at
      ⟨neg_abs_le time,le_abs_self time⟩

end SourceAbelianMomentAtlas

/-- Theorem 18.5(ii): local real analytic wellposedness at every higher-exponent source. -/
theorem renormalizedNLS_locallyAnalyticallyWellposed_of_two_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p) := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  intro φ
  obtain ⟨T,hT,U,hU,hφ,hsub,_⟩ := A.exists_local_analytic_renormalizedTrajectories hs hP hr D φ
  refine ⟨T,hT,U,hU,hφ,A.hamiltonianRenormalizedImageFlow D,?_,
    A.hamiltonianRenormalizedImageTrajectoryOn D T,
    (A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T).mono hsub,?_⟩
  · intro ψ hψ
    exact A.renormalizedImageFlow_isSolution hs hP hr D h2p ψ T hT.le (hsub hψ)
  · intro ψ hψ time
    exact A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T ψ (hsub hψ) time

/-- Renormalized NLS is locally real analytically wellposed at every finite p > 1. -/
theorem renormalizedNLS_locallyAnalyticallyWellposed (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsLocallyAnalyticallyWellposed (fun f : SmoothNLSData => f.renormalizedSource p) := by
  rcases le_total p 2 with hp2 | h2p
  · exact (renormalizedNLS_globallyAnalyticallyWellposed hp hp1 hp2).local
  · exact renormalizedNLS_locallyAnalyticallyWellposed_of_two_le hp hp1 h2p

/-- Theorem 18.5(iii): global analytic wellposedness on an actual open neighborhood
of zero, containing a positive source-norm ball, for every higher exponent. -/
theorem exists_small_global_analytic_renormalizedNLSSolutions
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ U : Set (realTypeSourceSubmodule p), (0 : realTypeSourceSubmodule p) ∈ U ∧
      (∃ r > 0, Metric.ball 0 r ⊆ U) ∧
      IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) U := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  obtain ⟨U,hU,hzero,hball,hvalid,_⟩ := A.exists_invariant_small_renormalizedFlow D
  refine ⟨U,hzero,hball,hU,A.hamiltonianRenormalizedImageFlow D,
    fun φ hφ => A.renormalizedImageFlow_isGlobalSolution hs hP hr D h2p U hvalid φ hφ,?_⟩
  intro T _
  have hsub : U ⊆ A.renormalizedTrajectoryDomain t T := fun φ hφ time => hvalid φ hφ time.val
  exact ⟨A.hamiltonianRenormalizedImageTrajectoryOn D T,
    (A.analytic_hamiltonianRenormalizedImageTrajectoryOn hs hP hr D T).mono hsub,
    fun φ hφ time => A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T φ (hsub hφ) time⟩

end NLS.ZakharovShabat
