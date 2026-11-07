import NLS.Articles.KdVPseudomeasures.SpectralResolvent
import NLS.KdV.PseudomeasureInhomogeneousReduction

/-!
# Analytic reconstruction for original complex source potentials

The parameters, right-hand sides and H1 solutions are original distributions.
The complex endpoint Banach norm is unchanged. These are dependencies for
algebraic-multiplicity comparison, not an assertion of that comparison.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
open NLS.KdV

/-- The physical H1 reconstruction parameterized by original source distributions. -/
def sourceEndpointReconstruction (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ)
    (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ) :
    (ℂ × ℂ) →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointReconstructionFamily r hr.1 hr.2 n (sourceEndpointCoefficients r p.1,p.2)

/-- The complementary response accepts arbitrary original endpoint right-hand sides. -/
def sourceEndpointResponse (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ)
    (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ) :
    FourierLebesgueSpace (2:ℝ) (-r) ⊤ →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (endpointResponseFamily r hr.1 hr.2 n (sourceEndpointCoefficients r p.1,p.2)).comp
    (sourceEndpointCoefficientsCLM r)

/-- Joint original-norm analyticity of the full H1 reconstruction, even at determinant zeros. -/
theorem analyticAt_sourceEndpointReconstruction (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (sourceEndpointReconstruction r hr n) p := by
  let P := (sourceEndpointCoefficientsCLM r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖(P p).1‖ ≤ 1/2 := by
    change endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r p.1‖ ≤ 1/2
    rwa [norm_sourceEndpointCoefficients]
  exact (analyticAt_endpointReconstructionFamily r hr.1 hr.2 n hn (P p) hz hsE).comp
    (P.analyticAt p)

/-- Joint original-norm analyticity of the complementary H1 response. -/
theorem analyticAt_sourceEndpointResponse (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (sourceEndpointResponse r hr n) p := by
  let P := (sourceEndpointCoefficientsCLM r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖(P p).1‖ ≤ 1/2 := by
    change endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r p.1‖ ≤ 1/2
    rwa [norm_sourceEndpointCoefficients]
  have hR := (analyticAt_endpointResponseFamily r hr.1 hr.2 n hn (P p) hz hsE).comp
    (P.analyticAt p)
  exact SchurComplement.analyticAt_compCLM hR analyticAt_const

/-- The actual original singular pencil is jointly analytic in original endpoint parameters. -/
theorem analyticAt_sourcePhysicalPencil (r : ℝ) (hr : AdmissiblePredualOrder r)
    (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ) :
    AnalyticAt ℂ (fun y : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ =>
      y.2 • singularHillDomainInclusion - singularHillOperator (sourceComplexHminusOne r hr y.1)) p := by
  let P := (sourceEndpointCoefficientsCLM r).prodMap (ContinuousLinearMap.id ℂ ℂ)
  have hP := (analyticAt_endpointPhysicalPencilFamily r hr.1 hr.2 (P p)).comp (P.analyticAt p)
  change AnalyticAt ℂ (fun y : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ =>
    endpointPhysicalPencilFamily r hr.2 (sourceEndpointCoefficients r y.1,y.2)) p at hP
  simpa only [endpointPhysicalPencilFamily,
    sourceEndpointCoefficients_HminusOne_complex r hr] using hP

/-- The source reconstruction keeps exactly its two normalized physical Fourier amplitudes. -/
theorem sourceEndpointReconstruction_coordinates (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (endpointHillH1Coordinates n).comp (sourceEndpointReconstruction r hr n p) =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  apply endpointReconstructionFamily_coordinates r hr.1 hr.2 n hn _ hz
  simpa only [norm_sourceEndpointCoefficients] using hs

/-- The source reconstruction has exactly the actual reduced resonant residual. -/
theorem sourceEndpointReconstruction_residual (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (p : FourierLebesgueSpace (2:ℝ) (-r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (p.2 • singularHillDomainInclusion - singularHillOperator (sourceComplexHminusOne r hr p.1)).comp
      (sourceEndpointReconstruction r hr n p) =
      singularHillDomainInclusion.comp ((endpointHillH1Modes n).comp
        (endpointReducedFamily r hr.1 hr.2 n (sourceEndpointCoefficients r p.1,p.2))) := by
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r p.1‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  simpa only [sourceEndpointReconstruction, endpointPhysicalPencilFamily,
    sourceEndpointCoefficients_HminusOne_complex r hr] using
    endpointReconstructionFamily_residual r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r p.1,p.2) hz hsE

/-- Exact inhomogeneous reduction for every original H1 solution, arbitrary
original endpoint forcing and all closed-strip points allowed by the cutoff. -/
theorem source_inhomogeneous_physical_reduction (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ)
    (hz : z ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (g : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    z • singularHillDomainInclusion f - singularHillOperator (sourceComplexHminusOne r hr q) f =
      sourceComplexHminusOne r hr g ↔
    f = sourceEndpointReconstruction r hr n (q,z) (endpointHillH1Coordinates n f) +
        sourceEndpointResponse r hr n (q,z) g ∧
      endpointReducedFamily r hr.1 hr.2 n (sourceEndpointCoefficients r q,z)
        (endpointHillH1Coordinates n f) =
        hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
          (endpointInverseFamily r hr.1 hr.2 n (sourceEndpointCoefficients r q,z)
            (sourceEndpointCoefficients r g)) := by
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  simpa only [sourceEndpointReconstruction, sourceEndpointResponse, ContinuousLinearMap.comp_apply,
    sourceEndpointCoefficientsCLM_apply, endpointPhysicalPencilFamily,
    sourceEndpointCoefficients_HminusOne_complex r hr, sub_apply, _root_.smul_apply] using
    endpointPhysicalPencil_inhomogeneous_iff r hr.1 hr.2 n hn z hz
      (sourceEndpointCoefficients r q) hsE (sourceEndpointCoefficients r g) f

/-- Actual determinant zeros lie strictly inside the corrected strip, so all
physical reconstruction identities are identities of spectral germs there. -/
theorem sourceEndpointDeterminant_zero_interior (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) :
    |z.re-freeHillValue n| < 6*(n:ℝ) := by
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  have hL := endpointReducedDeterminant_zero_localization r hr.1 hr.2 n hn
    (sourceEndpointCoefficients r q) hsE z hz hd
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hS : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hR : |z.re-freeHillValue n| ≤ ‖z-(freeHillValue n:ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  linarith

/-- At every actual determinant zero the reconstruction satisfies its exact
physical residual on a whole neighborhood in the spectral parameter. -/
theorem sourceEndpointReconstruction_residual_germ (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hd : sourceEndpointDeterminant r hr n (q,z) = 0) :
    (fun y : ℂ => (y • singularHillDomainInclusion -
      singularHillOperator (sourceComplexHminusOne r hr q)).comp
        (sourceEndpointReconstruction r hr n (q,y))) =ᶠ[𝓝 z]
    (fun y : ℂ => singularHillDomainInclusion.comp ((endpointHillH1Modes n).comp
      (endpointReducedFamily r hr.1 hr.2 n (sourceEndpointCoefficients r q,y)))) := by
  have hi := sourceEndpointDeterminant_zero_interior r hr n hn q hs z hz hd
  have hsE : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    simpa only [norm_sourceEndpointCoefficients] using hs
  simpa only [sourceEndpointReconstruction, endpointPhysicalPencilFamily,
    sourceEndpointCoefficients_HminusOne_complex r hr] using
    endpointReconstructionFamily_residual_germ r hr.1 hr.2 n hn
      (sourceEndpointCoefficients r q) z hi hsE

end NLS.Articles.KdVPseudomeasures
