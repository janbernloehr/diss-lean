import NLS.ZakharovShabat.SmoothPeriodOneSourceExponent
import NLS.ZakharovShabat.SmoothClassicalNLSAgreement
import NLS.ZakharovShabat.SourceRenormalizedImageClassicalAgreement

/-! # Classical agreement across source exponents

Every supplied classical trajectory is the coefficient-identical spectral
flow in the global range. The renormalized image flow also agrees at larger
exponents; smooth initial sources stay in its actual image at every time.
-/
noncomputable section
open Set NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every classical ordinary trajectory equals the global source flow
at each exponent between one and two, using its original Fourier data. -/
theorem classicalNLS_source_eq_flow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalNLSTrajectory u) (time : ℝ) :
    smoothPeriodOneSourceAt p (u time) (hu.spatial_smooth time) (hu.periodic time) =
      A.hamiltonianOrdinarySourceFlow D hp2
        (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time := by
  obtain ⟨W₂,P₂,_,_,hP₂,hr₂,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have he : realTypeSourceExponentInclusion hp2
      (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) =
      smoothPeriodOneHilbertSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0) :=
    (smoothPeriodOneSourceAt_exponent hp2 _ _ _).trans (smoothPeriodOneSourceAt_two _ _ _)
  have hi := A.hamiltonianOrdinarySourceFlow_exponent H hs hs₂.toSourcePsiIsolatingComplexExtension
    D E hp2 le_rfl (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time
  rw [he] at hi
  apply realTypeSource_eq_of_fst
  intro n
  exact (smoothPeriodOneSourceAt_fst _ _ _ n).trans
    ((H.classicalNLS_periodOneCoefficient_eq_smoothFlow hs₂ hP₂ hr₂ E u hu time n).trans
      (congrArg (fun ξ : realTypeSourceSubmodule 2 => ξ.val.fst n) hi).symm)

/-- Every classical renormalized trajectory equals the global source flow
at each exponent between one and two, using its original Fourier data. -/
theorem classicalRenormalizedNLS_source_eq_flow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u 0)) u) (time : ℝ) :
    smoothPeriodOneSourceAt p (u time) (hu.spatial_smooth time) (hu.periodic time) =
      A.hamiltonianRenormalizedSourceFlow D hp2
        (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time := by
  obtain ⟨W₂,P₂,_,_,hP₂,hr₂,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have he : realTypeSourceExponentInclusion hp2
      (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) =
      smoothPeriodOneHilbertSource (u 0) (hu.spatial_smooth 0) (hu.periodic 0) :=
    (smoothPeriodOneSourceAt_exponent hp2 _ _ _).trans (smoothPeriodOneSourceAt_two _ _ _)
  have hi := A.hamiltonianRenormalizedSourceFlow_exponent H hs hs₂.toSourcePsiIsolatingComplexExtension
    D E hp2 le_rfl (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time
  rw [he] at hi
  apply realTypeSource_eq_of_fst
  intro n
  exact (smoothPeriodOneSourceAt_fst _ _ _ n).trans
    ((H.classicalRenormalizedNLS_periodOneCoefficient_eq_smoothFlow hs₂ hP₂ hr₂ E u hu time n).trans
      (congrArg (fun ξ : realTypeSourceSubmodule 2 => ξ.val.fst n) hi).symm)

/-- Smooth physical sources stay in the actual image for all times above two.
This is a property of smooth sources, not a surjectivity assertion at p > 2. -/
theorem smoothPeriodOneSourceAt_mem_renormalizedImageDomain
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (h2p : 2 ≤ p)
    (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hper : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) (time : ℝ) :
    (-time,smoothPeriodOneSourceAt p f hf hper) ∈ A.renormalizedImageDomain t := by
  obtain ⟨W₂,P₂,_,_,_,_,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have hi := A.hilbert_inclusion_mem_renormalizedImageDomain hs D H
    hs₂.toSourcePsiIsolatingComplexExtension E h2p (smoothPeriodOneSourceAt 2 f hf hper) time
  simpa only [smoothPeriodOneSourceAt_exponent] using! hi

/-- At every finite exponent greater than one, the actual renormalized image
flow agrees with every classical trajectory with its own physical initial mass. -/
theorem classicalRenormalizedNLS_source_eq_imageFlow
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u 0)) u) (time : ℝ) :
    smoothPeriodOneSourceAt p (u time) (hu.spatial_smooth time) (hu.periodic time) =
      A.hamiltonianRenormalizedImageFlow D
        (smoothPeriodOneSourceAt p (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time := by
  rcases le_total p 2 with hp2 | h2p
  · rw [A.hamiltonianRenormalizedImageFlow_eq_global D hp2]
    exact A.classicalRenormalizedNLS_source_eq_flow hs D hp2 u hu time
  · obtain ⟨W₂,P₂,_,_,hP₂,hr₂,s₂,hs₂,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
    obtain ⟨V₂,B₂,X₂,t₂,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
    have hi := A.hamiltonianRenormalizedImageFlow_hilbert_inclusion hs D H
      hs₂.toSourcePsiIsolatingComplexExtension E h2p
      (smoothPeriodOneSourceAt 2 (u 0) (hu.spatial_smooth 0) (hu.periodic 0)) time
    rw [smoothPeriodOneSourceAt_exponent,smoothPeriodOneSourceAt_two] at hi
    apply realTypeSource_eq_of_fst
    intro n
    exact (smoothPeriodOneSourceAt_fst _ _ _ n).trans
      ((H.classicalRenormalizedNLS_periodOneCoefficient_eq_smoothFlow hs₂ hP₂ hr₂ E u hu time n).trans
        (congrArg (fun ξ : realTypeSourceSubmodule p => ξ.val.fst n) hi).symm)

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
