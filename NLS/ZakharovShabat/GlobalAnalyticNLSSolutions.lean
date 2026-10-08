import NLS.ZakharovShabat.AnalyticNLSWellposedness
import NLS.ZakharovShabat.SourceSmoothApproximationSolutions

/-! # Global analytic wellposedness for 1 < p ≤ 2

The actual approximation solutions depend real analytically on the initial
source in the uniform compact-time norm. All spectral objects are constructed
inside the proofs; the statements require only the source exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corollary 22.2(i), ordinary NLS, in the all-smooth-sequence solution sense. -/
theorem ordinaryNLS_globallyAnalyticallyWellposed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.ordinarySource p) univ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  refine ⟨isOpen_univ,A.hamiltonianOrdinarySourceFlow D hp2,
    fun φ _ => A.ordinarySourceFlow_isSolution hs hP hr D hp2 φ,?_⟩
  intro T _
  exact ⟨A.hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,
    A.analytic_hamiltonianOrdinarySourceTrajectoryOn hs hP hr D hp2 T,fun _ _ _ => rfl⟩

/-- Theorem 18.5(i) and the renormalized part of Corollary 22.2(i). -/
theorem renormalizedNLS_globallyAnalyticallyWellposed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    IsGloballyAnalyticallyWellposedOn (fun f : SmoothNLSData => f.renormalizedSource p) univ := by
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := p) hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := p) hp hp1
  refine ⟨isOpen_univ,A.hamiltonianRenormalizedSourceFlow D hp2,
    fun φ _ => A.renormalizedSourceFlow_isSolution hs hP hr D hp2 φ,?_⟩
  intro T _
  exact ⟨A.hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T,
    A.analytic_hamiltonianRenormalizedSourceTrajectoryOn hs hP hr D hp2 T,fun _ _ _ => rfl⟩

end NLS.ZakharovShabat
