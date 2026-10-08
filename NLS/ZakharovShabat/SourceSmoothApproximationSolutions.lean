import NLS.ZakharovShabat.SmoothApproximationSolution
import NLS.ZakharovShabat.ConstructedClassicalNLSApproximation

/-! # Spectral flows solve NLS in the all-smooth-sequence sense

The global low-exponent flows and admissible higher-exponent renormalized
paths satisfy the dissertation's actual approximation definition, using the
constructed classical solution of each arbitrary smooth initial datum.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The global ordinary source flow is an all-smooth-sequence solution. -/
theorem ordinarySourceFlow_isSolution
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    IsOrdinaryNLSSolutionOn univ φ (A.hamiltonianOrdinarySourceFlow D hp2 φ) := by
  refine ⟨mem_univ _,?_,A.hamiltonianOrdinarySourceFlow_zero D hp2 φ,?_⟩
  · exact ((A.continuous_hamiltonianOrdinarySourceFlow hs hP hr D hp2).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro f hf time _
    exact (A.tendstoUniformlyOn_constructedOrdinarySource hs hP hr D hp2 f φ hf |time|).tendsto_at
      ⟨neg_abs_le time,le_abs_self time⟩

/-- The global renormalized source flow is an all-smooth-sequence solution. -/
theorem renormalizedSourceFlow_isSolution
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    IsRenormalizedNLSSolutionOn univ φ (A.hamiltonianRenormalizedSourceFlow D hp2 φ) := by
  refine ⟨mem_univ _,?_,A.hamiltonianRenormalizedSourceFlow_zero D hp2 φ,?_⟩
  · exact ((A.continuous_hamiltonianRenormalizedSourceFlow hs hP hr D hp2).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro f hf time _
    exact (A.tendstoUniformlyOn_constructedRenormalizedSource hs hP hr D hp2 f φ hf |time|).tendsto_at
      ⟨neg_abs_le time,le_abs_self time⟩

/-- Every admissible compact higher-exponent trajectory is a renormalized solution. -/
theorem renormalizedImageFlow_isSolution
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) (T : ℝ) (hT : 0 ≤ T)
    (hφ : φ ∈ A.renormalizedTrajectoryDomain t T) :
    IsRenormalizedNLSSolutionOn (Icc (-T) T) φ (A.hamiltonianRenormalizedImageFlow D φ) := by
  refine ⟨⟨neg_nonpos.mpr hT,hT⟩,?_,A.hamiltonianRenormalizedImageFlow_zero D φ,?_⟩
  · apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (fun time : Icc (-T) T => A.hamiltonianRenormalizedImageFlow D φ time.val) =
        (A.hamiltonianRenormalizedImageTrajectoryOn D T φ : Icc (-T) T → realTypeSourceSubmodule p) := by
      funext time
      exact (A.hamiltonianRenormalizedImageTrajectoryOn_apply hs hP hr D T φ hφ time).symm
    change Continuous (fun time : Icc (-T) T => A.hamiltonianRenormalizedImageFlow D φ time.val)
    rw [he]
    exact (A.hamiltonianRenormalizedImageTrajectoryOn D T φ).continuous
  · intro f hf time ht
    exact (A.tendstoUniformlyOn_constructedRenormalizedImageSource hs hP hr D h2p f φ hf T hφ).tendsto_at ht

end SourceAbelianMomentAtlas

/-- Every real source in the global exponent range has exactly one ordinary
solution in the dissertation's approximation sense. Spectral data are internal. -/
theorem existsUnique_global_ordinaryNLSSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    ∃! γ : ℝ → realTypeSourceSubmodule p, IsOrdinaryNLSSolutionOn univ φ γ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  have hγ := A.ordinarySourceFlow_isSolution hs hP hr D hp2 φ
  refine ⟨A.hamiltonianOrdinarySourceFlow D hp2 φ,hγ,?_⟩
  intro η hη
  funext time
  exact hη.eqOn_inter hγ hp hp1 ⟨mem_univ time,mem_univ time⟩

/-- Every real source in the global exponent range has exactly one renormalized
solution in the dissertation's approximation sense. -/
theorem existsUnique_global_renormalizedNLSSolution
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) :
    ∃! γ : ℝ → realTypeSourceSubmodule p, IsRenormalizedNLSSolutionOn univ φ γ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  have hγ := A.renormalizedSourceFlow_isSolution hs hP hr D hp2 φ
  refine ⟨A.hamiltonianRenormalizedSourceFlow D hp2 φ,hγ,?_⟩
  intro η hη
  funext time
  exact hη.eqOn_inter hγ hp hp1 ⟨mem_univ time,mem_univ time⟩

end NLS.ZakharovShabat
