import NLS.KdV.PseudomeasureH1Analytic
import NLS.KdV.PseudomeasureCoefficients
import NLS.KdV.PseudomeasureBilinearSymmetry

/-!
# Analytic reconstruction on the full physical singular Hill domain

Only the complementary inverse is used. The reconstruction and its physical
residual are analytic even when the effective two-dimensional determinant
vanishes. At interior strip points the exact residual identity holds as a
germ in the spectral parameter, as required for Taylor root-chain arguments.
-/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The original physical pencil `lambda J - L(q)` as one total operator family. -/
def endpointPhysicalPencilFamily (r : ℝ) (hr1 : r < 1/2)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  p.2 • singularHillDomainInclusion -
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 p.1)

/-- The singular physical pencil is jointly norm-analytic on the full parameter space. -/
theorem analyticAt_endpointPhysicalPencilFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    AnalyticAt ℂ (endpointPhysicalPencilFamily r hr1) p := by
  have hq := ((WeightedCoeff.signedSobolevConvolutionBilinear r hr).analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  have hM := SchurComplement.analyticAt_compCLM
    (analyticAt_const (v := endpointHillHminusOne SpectralWeight.one r hr1))
    (SchurComplement.analyticAt_compCLM hq (analyticAt_const (v := endpointH1ToWiener r hr1)))
  have hz := (ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p
  have he : endpointPhysicalPencilFamily r hr1 = fun y =>
      y.2 • singularHillDomainInclusion -
        (singularHillLaplacian + (endpointHillHminusOne SpectralWeight.one r hr1).comp
          ((WeightedCoeff.signedSobolevConvolutionBilinear r hr y.1).comp (endpointH1ToWiener r hr1))) := by
    funext y
    apply ContinuousLinearMap.ext
    intro f
    simp only [endpointPhysicalPencilFamily, singularHillOperator, sub_apply]
    rw [WeightedCoeff.signedSobolevConvolutionBilinear_eq]
    exact congrArg (fun v => y.2 • singularHillDomainInclusion f - (singularHillLaplacian f + v))
      (endpointH1Multiplication_physical r hr hr1 y.1 f).symm
  rw [he]
  exact (hz.smul analyticAt_const).sub (analyticAt_const.add hM)

/-- A proof-independent analytic reconstruction family with full original H1 values. -/
def endpointReconstructionFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) :
    (ℂ × ℂ) →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  endpointHillH1Modes n +
    (endpointH1ResolventFamily r hr1 n p.2).comp (endpointEffectiveFamily r hr hr1 n p)

/-- The total analytic family is exactly the actual physical reconstruction. -/
theorem endpointReconstructionFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointReconstructionFamily r hr hr1 n p =
      endpointHillReconstruct r hr hr1 n hn p.2 hz p.1 hs := by
  unfold endpointReconstructionFamily endpointHillReconstruct
  rw [endpointH1ResolventFamily_eq r hr1 n hn p.2 hz,
    endpointEffectiveFamily_eq r hr hr1 n hn p hz hs]

/-- Joint operator-norm analyticity of full-domain reconstruction, including determinant zeros. -/
theorem analyticAt_endpointReconstructionFamily (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointReconstructionFamily r hr hr1 n) p := by
  have hR := (analyticAt_endpointH1ResolventFamily r hr1 n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) ℂ).analyticAt p)
  have hE := SchurComplement.analyticAt_compCLM
    (analyticAt_endpointInverseFamily r hr hr1 n hn p hz hs)
    (analyticAt_endpointModePotentialFamily r hr hr1 n p)
  exact analyticAt_const.add (SchurComplement.analyticAt_compCLM hR hE)

/-- Reconstruction retains the original two amplitudes as an operator identity. -/
theorem endpointReconstructionFamily_coordinates (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (endpointHillH1Coordinates n).comp (endpointReconstructionFamily r hr hr1 n p) =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  rw [endpointReconstructionFamily_eq r hr hr1 n hn p hz hs]
  apply ContinuousLinearMap.ext
  intro u
  exact endpointHillH1Coordinates_reconstruct r hr hr1 n hn p.2 hz p.1 hs u

/-- The exact physical residual identity in the original H-minus-one target. -/
theorem endpointReconstructionFamily_residual (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    (endpointPhysicalPencilFamily r hr1 p).comp (endpointReconstructionFamily r hr hr1 n p) =
      singularHillDomainInclusion.comp ((endpointHillH1Modes n).comp (endpointReducedFamily r hr hr1 n p)) := by
  rw [endpointReconstructionFamily_eq r hr hr1 n hn p hz hs,
    endpointReducedFamily_eq r hr hr1 n hn p hz hs]
  apply ContinuousLinearMap.ext
  intro u
  exact endpointHillReconstruct_residual_equation r hr hr1 n hn p.2 hz p.1 hs u

/-- Original H1 reconstruction is analytic in lambda at every allowed closed-strip point. -/
theorem analyticAt_endpointReconstruction_spectral (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    AnalyticAt ℂ (fun y : ℂ => endpointReconstructionFamily r hr hr1 n (q,y)) z :=
  (analyticAt_endpointReconstructionFamily r hr hr1 n hn (q,z) hz hs).comp
    (f := fun y : ℂ => (q,y)) (analyticAt_const.prod analyticAt_id)

/-- A strictly interior strip point has a whole neighborhood in the corrected closed strip. -/
theorem eventually_mem_reducedHillStrip (n : ℕ) (z : ℂ)
    (hz : |z.re-freeHillValue n| < 6*(n:ℝ)) :
    ∀ᶠ y in 𝓝 z, y ∈ reducedHillStrip n := by
  have hc : Continuous (fun y : ℂ => |y.re-freeHillValue n|) :=
    (Complex.continuous_re.sub continuous_const).abs
  exact ((hc.tendsto z).eventually (gt_mem_nhds hz)).mono fun _ hy => hy.le

/-- The physical residual identity holds as a spectral germ at every interior point. -/
theorem endpointReconstructionFamily_residual_germ (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    (fun y : ℂ => (endpointPhysicalPencilFamily r hr1 (q,y)).comp
      (endpointReconstructionFamily r hr hr1 n (q,y))) =ᶠ[𝓝 z]
      (fun y : ℂ => singularHillDomainInclusion.comp
        ((endpointHillH1Modes n).comp (endpointReducedFamily r hr hr1 n (q,y)))) := by
  filter_upwards [eventually_mem_reducedHillStrip n z hz] with y hy
  exact endpointReconstructionFamily_residual r hr hr1 n hn (q,y) hy hs

/-- The constant resonant-coordinate left inverse also holds as a spectral germ. -/
theorem endpointReconstructionFamily_coordinates_germ (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (z : ℂ) (hz : |z.re-freeHillValue n| < 6*(n:ℝ))
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    (fun y : ℂ => (endpointHillH1Coordinates n).comp
      (endpointReconstructionFamily r hr hr1 n (q,y))) =ᶠ[𝓝 z]
      (fun _ : ℂ => ContinuousLinearMap.id ℂ (ℂ × ℂ)) := by
  filter_upwards [eventually_mem_reducedHillStrip n z hz] with y hy
  exact endpointReconstructionFamily_coordinates r hr hr1 n hn (q,y) hy hs

end NLS.KdV
