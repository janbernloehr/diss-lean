import NLS.ComplexAnalysis.RealAnalyticNeighborhoodExtension
import NLS.ComplexAnalysis.ContinuousMapSuperposition

/-! A globally real analytic map between contractive real forms acts
real analytically on compact continuous-function spaces in the UNIFORM
Banach norm. A holomorphic neighborhood of the entire real source
supplies the uniform compact-range analyticity. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {K R E S F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem analyticAt_real_superposition (c : ContractiveComplexification R E)
    (d : ContractiveComplexification S F) (hnorm : ∀ x, ‖c.inclusion x‖=‖x‖)
    (f : R → S) (hf : ∀ x, AnalyticAt ℝ f x) (a : C(K,R)) :
    AnalyticAt ℝ (superposition (K := K) f) a := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hi (x : R) : AnalyticAt ℝ (fun y => d.inclusion (f y)) x :=
    (d.inclusion.analyticAt _).comp (f := f) (hf x)
  obtain ⟨U,hU,hreal,G,hG,hagree⟩ := c.exists_complex_extension_neighborhood hnorm
    (fun x => d.inclusion (f x)) hi
  let J : C(K,R) →L[ℝ] C(K,E) := c.inclusion.compLeftContinuous ℝ K
  let D : C(K,F) →L[ℝ] C(K,S) := d.re.compLeftContinuous ℝ K
  have hJU (b : C(K,R)) : range (J b) ⊆ U := by
    rintro _ ⟨t,rfl⟩
    exact hreal (b t)
  have hA : AnalyticAt ℝ (superposition (K := K) G) (J a) :=
    (analyticOnNhd_superposition hU hG _ (hJU a)).restrictScalars
  have hcomp : AnalyticAt ℝ (fun b : C(K,R) => D (superposition G (J b))) a :=
    (D.analyticAt _).comp (f := fun b : C(K,R) => superposition G (J b))
      (hA.comp (f := J) (J.analyticAt a))
  apply hcomp.congr
  apply Filter.Eventually.of_forall
  intro b
  apply ContinuousMap.ext
  intro t
  change d.re (superposition G (J b) t)=superposition f b t
  rw [superposition_apply hG.continuousOn (hJU b) t]
  change d.re (G (c.inclusion (b t)))=superposition f b t
  rw [hagree,d.re_inclusion,superposition_apply (U := univ) hfc.continuousOn (subset_univ _) t]

end NLS.ComplexAnalysis
