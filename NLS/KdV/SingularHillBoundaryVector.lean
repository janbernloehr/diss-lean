import NLS.KdV.HillH1ParityRepresentative
import NLS.FunctionalAnalysis.UnitFunctionalKernel

/-! A genuine normalized zero-at-origin vector in every actual two-dimensional
native Hill spectral range, with no supplied basis or trace-zero witness. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- An ACTUAL rank-two physical spectral range contains a native H1 vector
of physical L2 norm ONE whose IDENTICAL continuous representative vanishes
at zero. All complex associated-vector directions are allowed. -/
theorem exists_singularHill_boundaryZero_spectralVector
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q)
    (hd : Module.finrank ℂ (singularHillL2RieszProjection q c rho).range=2) :
    ∃ G : FourierLebesgueSpace (2:ℝ) 1 2,
      ‖singularHillL2DomainInclusion G‖=1 ∧
      singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection q c rho).range ∧
      singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ))=0 := by
  let P := singularHillL2RieszProjection q c rho
  let S := P.range
  let : FiniteDimensional ℂ S := finiteDimensional_singularHillL2RieszProjection_range q c rho hrho hc
  let H := (singularHillRieszToH1 q c rho).comp singularHillL2BaseInclusion
  let L : S →L[ℂ] ℂ := ((ContinuousMap.evalCLM ℂ (0 : AddCircle (2:ℝ))).comp
    (singularHillContinuousDomainInclusion.comp H)).comp S.subtypeL
  obtain ⟨x,hx,htrace⟩ := NLS.FunctionalAnalysis.exists_unit_mem_functional_kernel
    (E := S) (by change 1 < Module.finrank ℂ P.range;rw [hd];norm_num) L
  let G := H x.val
  have hphysical : singularHillL2DomainInclusion G=x.val := by
    change P x.val=x.val
    obtain ⟨Y,hY⟩ := x.property
    rw [← hY]
    exact congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T Y)
      (isIdempotentElem_singularHillL2RieszProjection q c rho hrho hc)
  refine ⟨G,?_,?_,?_⟩
  · rw [hphysical]
    exact hx
  · rw [hphysical]
    exact x.property
  · exact htrace

end NLS.KdV
