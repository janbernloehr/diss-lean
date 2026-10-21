import NLS.ZakharovShabat.ScalarNonlinearParseval
import NLS.ZakharovShabat.PhysicalBirkhoffLinearization

/-! # scalar Fourier differential at zero

The scalar map uses the original L2 input and normalized complex target. Its real differential at zero has the exact signed reflected Fourier coefficients.
-/

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The scalar physical embedding is real linear in its actual L2 classes. -/
def scalarPhysicalRealInputLinear : IntervalL2 →ₗ[ℝ] physicalRealSubmodule where
  toFun := scalarPhysicalRealInput
  map_add' u v := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change (u+v,star (u+v)) = (u+v,star u+star v)
    congr 1
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (u+v),Lp.coeFn_add u v,
      Lp.coeFn_add (star u) (star v),Lp.coeFn_star u,Lp.coeFn_star v] with x hs ha hb hu hv
    simp only [hs,ha,hb,Pi.add_apply,hu,hv,Pi.star_apply,star_add]
  map_smul' r u := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change (r • u,star (r • u)) = (r • u,r • star u)
    congr 1
    apply Lp.ext
    filter_upwards [Lp.coeFn_star (r • u),Lp.coeFn_smul r u,
      Lp.coeFn_smul r (star u),Lp.coeFn_star u] with x hs ha hb hu
    simp only [hs,ha,hb,Pi.smul_apply,hu,Pi.star_apply,star_smul,star_trivial]

/-- The exact scalar embedding is bounded in the original physical norm. -/
def scalarPhysicalRealInputCLM : IntervalL2 →L[ℝ] physicalRealSubmodule :=
  scalarPhysicalRealInputLinear.mkContinuous 2 (fun u => by
    change ‖scalarPhysicalRealInput u‖ ≤ 2*‖u‖
    have h := norm_sq_scalarPhysicalRealInput u
    nlinarith [norm_nonneg (scalarPhysicalRealInput u),norm_nonneg u])

/-- Read the normalized first complex coordinate from the native real Hilbert target. -/
def normalizedPhysicalScalarCoordinate : PhysicalRealBirkhoffTarget →L[ℝ] Coeff 2 :=
  (ContinuousLinearMap.fst ℝ (Coeff 2) (Coeff 2)).comp
    (Birkhoff.encodeReal.comp physicalRealTargetEquiv.toContinuousLinearMap)

/-- The normalized scalar nonlinear transform is real analytic on physical L2. -/
theorem scalarNonlinearFourier_analytic : AnalyticOnNhd ℝ scalarNonlinearFourier univ := by
  intro u _
  exact (normalizedPhysicalScalarCoordinate.analyticAt _).comp
    ((intrinsicPhysicalBirkhoffMap_analytic _ (mem_univ _)).comp
      (scalarPhysicalRealInputCLM.analyticAt u))

/-- The scalar nonlinear transform vanishes at the zero physical input. -/
theorem scalarNonlinearFourier_zero : scalarNonlinearFourier 0 = 0 := by
  apply norm_eq_zero.mp
  rw [scalarNonlinearFourier_norm,norm_zero]

/-- The full bounded scalar differential retains both physical embedding and target normalization. -/
theorem scalarNonlinearFourier_hasFDerivAt_zero :
    HasFDerivAt scalarNonlinearFourier
      (normalizedPhysicalScalarCoordinate.comp
        ((fderiv ℝ intrinsicPhysicalBirkhoffMap 0).comp scalarPhysicalRealInputCLM)) 0 := by
  have hi := (intrinsicPhysicalBirkhoffMap_analytic 0 (mem_univ _)).differentiableAt.hasFDerivAt
  have hi' : HasFDerivAt intrinsicPhysicalBirkhoffMap
      (fderiv ℝ intrinsicPhysicalBirkhoffMap 0) (scalarPhysicalRealInputCLM 0) := by
    simpa only [map_zero] using hi
  exact normalizedPhysicalScalarCoordinate.hasFDerivAt.comp 0
    (hi'.comp 0 scalarPhysicalRealInputCLM.hasFDerivAt)

/-- Each coefficient of the full scalar differential is the signed reflected physical Fourier integral. -/
theorem scalarNonlinearFourier_fderiv_zero_apply (u : IntervalL2) (n : ℤ) :
    fderiv ℝ scalarNonlinearFourier 0 u n =
      -NLS.Fourier.intervalFourierCoefficient 1 u (-n) := by
  rw [scalarNonlinearFourier_hasFDerivAt_zero.fderiv]
  have he := intrinsicPhysicalBirkhoffMap_fderiv_zero_complex (scalarPhysicalRealInput u)
  have hf := congrArg (fun z : CoeffPair 2 =>
    (Birkhoff.rectangularToComplex z.ofLp).1 n) he
  change normalizedPhysicalScalarCoordinate
    (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 (scalarPhysicalRealInput u)) n = _ at hf
  change normalizedPhysicalScalarCoordinate
    (fderiv ℝ intrinsicPhysicalBirkhoffMap 0 (scalarPhysicalRealInput u)) n = _
  apply hf.trans
  rw [Birkhoff.rectangularToComplex_fst]
  change Birkhoff.complexCoordinateScale *
    ((physicalBirkhoffFourier (scalarPhysicalRealInput u).val).fst n-
      I*(physicalBirkhoffFourier (scalarPhysicalRealInput u).val).snd n) = _
  rw [physicalBirkhoffFourier_fst,physicalBirkhoffFourier_snd]
  change Birkhoff.complexCoordinateScale *
    (-(NLS.Fourier.intervalFourierCoefficient 1 u (-n)+
        NLS.Fourier.intervalFourierCoefficient 1 (star u : IntervalL2) n)/(Real.sqrt 2:ℂ)-
      I*((NLS.Fourier.intervalFourierCoefficient 1 u (-n)-
        NLS.Fourier.intervalFourierCoefficient 1 (star u : IntervalL2) n)/((Real.sqrt 2:ℂ)*I))) = _
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hn : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  unfold Birkhoff.complexCoordinateScale
  field_simp [hn,I_ne_zero]
  ring_nf
  simp only [hs]

end NLS.ZakharovShabat
