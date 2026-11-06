import NLS.KdV.HillOriginalRealSpectralAnalytic
import NLS.FunctionalAnalysis.NormPreservingDerivative
import NLS.KdV.HillOriginalSpectralCompactPreimages

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The literal zero Fourier coefficient on the original real Banach space. -/
def hillOriginalRealZeroMode : hillRealSourceSubmodule →L[ℝ] ℂ :=
  (((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) 2 0).comp SpectralWeight.one.toCoeff).restrictScalars ℝ).comp
    hillRealSourceSubmodule.subtypeL

/-- The actual original real mean-zero Banach source, as a closed linear subspace. -/
def hillRealMeanZeroSourceSubmodule : Submodule ℝ hillRealSourceSubmodule :=
  hillOriginalRealZeroMode.ker

theorem mem_hillRealMeanZeroSourceSubmodule (q : hillRealSourceSubmodule) :
    q ∈ hillRealMeanZeroSourceSubmodule ↔ q.val.val 0 = 0 := by
  change SpectralWeight.one.toCoeff q.val 0 = 0 ↔ q.val.val 0 = 0
  rw [SpectralWeight.toCoeff_apply]

instance : CompleteSpace hillRealMeanZeroSourceSubmodule :=
  hillOriginalRealZeroMode.isClosed_ker.completeSpace_coe

/-- The ACTUAL original spectral sequence on its original mean-zero Banach domain. -/
def hillOriginalMeanZeroRealSpectralMap (q : hillRealMeanZeroSourceSubmodule) : lp (fun _ : ℕ => ℂ) 2 :=
  hillOriginalRealSpectralMap q.val

/-- No source norm is changed by representing the literal mean-zero condition
as a real Banach kernel. The spectral norm is the exact original trace. -/
theorem norm_hillOriginalMeanZeroRealSpectralMap (q : hillRealMeanZeroSourceSubmodule) :
    ‖hillOriginalMeanZeroRealSpectralMap q‖ = ‖q‖ :=
  norm_hillOriginalBaseSpectralSequence ⟨q.val.val,q.val.property⟩
    ((mem_hillRealMeanZeroSourceSubmodule q.val).mp q.property)

/-- The original mean-zero sequence map is real Banach analytic everywhere. -/
theorem analyticOnNhd_hillOriginalMeanZeroRealSpectralMap :
    AnalyticOnNhd ℝ hillOriginalMeanZeroRealSpectralMap univ := by
  intro q _
  exact (analyticOnNhd_hillOriginalRealSpectralMap q.val (mem_univ _)).comp
    (f := hillRealMeanZeroSourceSubmodule.subtypeL) (hillRealMeanZeroSourceSubmodule.subtypeL.analyticAt q)

/-- The actual original derivative at zero, with its exact original source
and target norms. Surjectivity and Fourier orientation are not assumptions. -/
def hillOriginalMeanZeroDerivativeAtZero : hillRealMeanZeroSourceSubmodule →L[ℝ] lp (fun _ : ℕ => ℂ) 2 :=
  fderiv ℝ hillOriginalMeanZeroRealSpectralMap 0

/-- The original physical spectral map vanishes at the literal zero source. -/
theorem hillOriginalMeanZeroRealSpectralMap_zero : hillOriginalMeanZeroRealSpectralMap 0 = 0 :=
  norm_eq_zero.mp (by rw [norm_hillOriginalMeanZeroRealSpectralMap,norm_zero])

/-- The exact quadratic action trace forces the ACTUAL zero-source
sequence derivative to preserve every original mean-zero L2 norm. -/
theorem norm_hillOriginalMeanZeroDerivativeAtZero (h : hillRealMeanZeroSourceSubmodule) :
    ‖hillOriginalMeanZeroDerivativeAtZero h‖ = ‖h‖ :=
  NLS.FunctionalAnalysis.norm_derivative_zero_of_norm_map hillOriginalMeanZeroRealSpectralMap
    hillOriginalMeanZeroDerivativeAtZero
    (analyticOnNhd_hillOriginalMeanZeroRealSpectralMap 0 (mem_univ _)).differentiableAt.hasFDerivAt
    norm_hillOriginalMeanZeroRealSpectralMap h

/-- The actual zero-source derivative as its proved real linear isometry. -/
def hillOriginalMeanZeroDerivativeAtZeroIsometry :
    hillRealMeanZeroSourceSubmodule →ₗᵢ[ℝ] lp (fun _ : ℕ => ℂ) 2 where
  toLinearMap := hillOriginalMeanZeroDerivativeAtZero.toLinearMap
  norm_map' := norm_hillOriginalMeanZeroDerivativeAtZero

/-- No nonzero original mean-zero source direction is lost by the
ACTUAL original spectral derivative at zero. -/
theorem injective_hillOriginalMeanZeroDerivativeAtZero :
    Function.Injective hillOriginalMeanZeroDerivativeAtZero :=
  hillOriginalMeanZeroDerivativeAtZeroIsometry.injective

/-- The original zero-source spectral derivative has closed range in the
actual base sequence Hilbert space. -/
theorem isClosed_range_hillOriginalMeanZeroDerivativeAtZero :
    IsClosed (range hillOriginalMeanZeroDerivativeAtZero) :=
  hillOriginalMeanZeroDerivativeAtZeroIsometry.isometry.isClosedEmbedding.isClosed_range

/-- The Banach-kernel domain is exactly the original mean-zero physical
domain, with both directions continuous in the original L2 topology. -/
def hillOriginalMeanZeroSourceHomeomorph : hillRealMeanZeroSourceSubmodule ≃ₜ HillOriginalMeanZeroSource where
  toFun q := ⟨⟨q.val.val,q.val.property⟩,(mem_hillRealMeanZeroSourceSubmodule q.val).mp q.property⟩
  invFun q := ⟨⟨q.val.val,q.val.property⟩,(mem_hillRealMeanZeroSourceSubmodule _).mpr q.property⟩
  left_inv q := by rfl
  right_inv q := by rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Properness holds on the ACTUAL original real Banach mean-zero domain
used for its derivative calculus. -/
theorem isProperMap_hillOriginalMeanZeroRealSpectralMap :
    IsProperMap hillOriginalMeanZeroRealSpectralMap := by
  have he : hillOriginalMeanZeroRealSpectralMap =
      hillOriginalMeanZeroBaseSpectralMap ∘ hillOriginalMeanZeroSourceHomeomorph := by
    funext q
    change hillOriginalBaseSpectralSequence (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential) =
      hillOriginalBaseSpectralSequence (⟨q.val.val,q.val.property⟩ : RealPeriodOneHillPotential)
    rfl
  rw [he]
  exact isProperMap_hillOriginalMeanZeroBaseSpectralMap.comp hillOriginalMeanZeroSourceHomeomorph.isProperMap

end NLS.KdV
