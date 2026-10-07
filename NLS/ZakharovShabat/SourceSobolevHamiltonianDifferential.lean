import NLS.ZakharovShabat.SourceSobolevHamiltonianIdentification
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # The physical correction identity as a full complex H¹ differential

Normalized weighted coordinates carry the H¹ real form to the original
Hilbert source real form. Analytic uniqueness therefore upgrades agreement
on real H¹ sources to equality of complex germs, and hence to equality of
the full complex Banach derivatives.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- Analytic H¹ maps agreeing on all real sources have identical complex germs. -/
theorem eventuallyEq_sobolev_of_analyticAt_of_real_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (a : realTypeSobolevSourceLocus) (f g : (ScalarDomain 2 × ScalarDomain 2) → F)
    (hf : AnalyticAt ℂ f a.val) (hg : AnalyticAt ℂ g a.val)
    (hreal : ∀ b : realTypeSobolevSourceLocus, f b.val = g b.val) :
    f =ᶠ[𝓝 a.val] g := by
  let E := sobolevNormalizedCoordinates
  let φ : realTypeSourceLocus 2 :=
    ⟨E a.val,(sobolevNormalizedCoordinates_realType_iff a.val).mpr a.property⟩
  have hf' : AnalyticAt ℂ (f ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (x := φ.val) (f := E.symm)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hf
    · exact E.symm.analyticAt _
  have hg' : AnalyticAt ℂ (g ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (x := φ.val) (f := E.symm)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hg
    · exact E.symm.analyticAt _
  have he := eventuallyEq_source_of_analyticAt_of_real_agreement (by simp) φ
    (f ∘ E.symm) (g ∘ E.symm) hf' hg' (fun ψ => by
      have hr : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (E.symm ψ.val))) :=
        (sobolevNormalizedCoordinates_realType_iff _).mp (by
          change IsRealType (CoeffPair.toMax 2 (E (E.symm ψ.val)))
          rw [E.apply_symm_apply]
          exact ψ.property)
      exact hreal ⟨E.symm ψ.val,hr⟩)
  have ht : Tendsto E (𝓝 a.val) (𝓝 φ.val) := E.continuous.continuousAt.tendsto
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using he.comp_tendsto ht

namespace SourcePrimitivePowerAtlas
open scoped ENNReal
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W : Set (CoeffPair 4)}

/-- The physical correction and FL⁴ Hamiltonian agree on a complex H¹ neighborhood of each real source. -/
theorem eventually_renormalizedHamiltonian_eq_sobolevPhysicalCorrection
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (a : realTypeSobolevSourceLocus) :
    (A.renormalizedHamiltonian ∘ sobolevSourceFL4) =ᶠ[𝓝 a.val] sourceSobolevPhysicalCorrection := by
  obtain ⟨U,_,_,hr,_,hA,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  obtain ⟨V,_,hrV,hV,_⟩ := exists_sourceSobolevPhysicalCorrection_analytic_domain
  apply eventuallyEq_sobolev_of_analyticAt_of_real_agreement a
  · exact (hA (realSobolevSourceFL4 a).val (hr (realSobolevSourceFL4 a).property)).comp
      (f := sobolevSourceFL4) (sobolevSourceFL4.analyticAt a.val)
  · exact hV a.val (hrV a.property)
  · exact A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection

/-- The physical H¹ correction has the restricted full FL⁴ complex differential. -/
theorem sobolevPhysicalCorrection_fderiv
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (a : realTypeSobolevSourceLocus) :
    fderiv ℂ sourceSobolevPhysicalCorrection a.val =
      (fderiv ℂ A.renormalizedHamiltonian (sobolevSourceFL4 a.val)).comp sobolevSourceFL4 := by
  obtain ⟨U,_,_,hr,_,hA,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  rw [← (A.eventually_renormalizedHamiltonian_eq_sobolevPhysicalCorrection a).fderiv_eq]
  rw [fderiv_comp a.val
    (hA (realSobolevSourceFL4 a).val (hr (realSobolevSourceFL4 a).property)).differentiableAt
      sobolevSourceFL4.differentiableAt,ContinuousLinearMap.fderiv]

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
