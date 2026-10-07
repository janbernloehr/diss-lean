import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.ZakharovShabat.SourceFiniteGapSobolevTime
import NLS.ZakharovShabat.SourceFiniteGapPhysicalNLSODE

/-! # The actual finite-gap trajectory solves physical NLS pointwise

The H¹ time derivative has the previously identified physical NLS Fourier
coefficients. Continuous periodic uniqueness identifies its synthesis with
the classical spatial field. Bounded evaluation then gives the actual
pointwise time equation, with the Hamiltonian sign and unit-period scale.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The H¹ vector with the physical NLS source coefficients synthesizes
to the actual classical spatial field at every point. -/
theorem periodOneSobolevSynthesis_eq_finiteGapPhysicalNLS
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (v : ScalarDomain 2 × ScalarDomain 2)
    (hv : sobolevSourceInclusion v = sourceFiniteGapPhysicalNLSCoefficients φ hf) :
    (fun x : ℝ => periodOneSobolevSynthesis v.1 (x : AddCircle (2 : ℝ))) =
      (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1 ∧
    (fun x : ℝ => periodOneSobolevSynthesis v.2 (x : AddCircle (2 : ℝ))) =
      (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2 := by
  have hreg := sourceFiniteGapPhysicalNLSVectorField_regular (by simp) (by norm_num) φ hf
  constructor
  · apply periodOneSobolevSynthesis_eq_of_coefficients v.1 _ hreg.1.1.continuous hreg.2.1
    intro n
    have he := congrArg (fun a : CoeffPair 2 => a.fst n) hv
    rw [sobolevSourceInclusion_fst,(sourceFiniteGapPhysicalNLSCoefficients_apply φ hf n).1] at he
    exact he
  · apply periodOneSobolevSynthesis_eq_of_coefficients v.2 _ hreg.1.2.continuous hreg.2.2
    intro n
    have he := congrArg (fun a : CoeffPair 2 => a.snd n) hv
    rw [sobolevSourceInclusion_snd,(sourceFiniteGapPhysicalNLSCoefficients_apply φ hf n).2] at he
    exact he

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical pair of the constructed Hamiltonian-oriented finite-gap trajectory. -/
def hamiltonianOrdinaryPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  sourceFiniteGapPhysicalPair (by simp) (by norm_num)
    (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)

@[simp] theorem hamiltonianOrdinaryPhysicalFlow_zero
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    A.hamiltonianOrdinaryPhysicalFlow D φ hf 0 = sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf := by
  simp [hamiltonianOrdinaryPhysicalFlow]

/-- Both physical components stay smooth and period one in space. -/
theorem hamiltonianOrdinaryPhysicalFlow_regular
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    (ContDiff ℝ ∞ (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 ∧
      ContDiff ℝ ∞ (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).2) ∧
    (Function.Periodic (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 1 ∧
      Function.Periodic (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).2 1) :=
  ⟨contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _,
    periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _⟩

/-- The actual physical trajectory retains the conjugate-pair real form. -/
theorem hamiltonianOrdinaryPhysicalFlow_real
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).2 x =
      (starRingEnd ℂ) ((A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 x) :=
  sourceFiniteGapPhysicalPair_real (by simp) (by norm_num) _ _ x

/-- The H¹ time derivative has exactly the original physical NLS Fourier coefficients. -/
theorem sobolev_timeDerivative_hamiltonianOrdinarySourceFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    sobolevSourceInclusion (deriv (fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ r)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf r)) time) =
      sourceFiniteGapPhysicalNLSCoefficients (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
        (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time) := by
  have hd := (A.differentiable_hamiltonianOrdinarySourceFlow_sobolev D φ hf time).hasDerivAt
  have hi := (sobolevSourceInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  change HasDerivAt (fun r => sobolevSourceInclusion (sourceFiniteGapSobolevPair
    (by simp) (by norm_num) (A.hamiltonianOrdinarySourceFlow D le_rfl φ r)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf r))) _ time at hi
  simp only [sobolevSourceInclusion_sourceFiniteGapSobolevPair] at hi
  exact hi.unique (A.hasDerivAt_hamiltonianOrdinarySourceFlow_physicalNLS hs D φ hf time)

/-- Both actual pointwise time derivatives are the classical NLS spatial field. -/
theorem hasDerivAt_hamiltonianOrdinaryPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := A.hamiltonianOrdinaryPhysicalFlow D φ hf
    HasDerivAt (fun r => (u r).1 x) ((classicalNLSVectorField (u time).1 (u time).2).1 x) time ∧
    HasDerivAt (fun r => (u r).2 x) ((classicalNLSVectorField (u time).1 (u time).2).2 x) time := by
  dsimp only
  let q := fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num)
    (A.hamiltonianOrdinarySourceFlow D le_rfl φ r)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf r)
  have hd : HasDerivAt q (deriv q time) time :=
    (A.differentiable_hamiltonianOrdinarySourceFlow_sobolev D φ hf time).hasDerivAt
  have hvel := periodOneSobolevSynthesis_eq_finiteGapPhysicalNLS _ _ (deriv q time)
    (A.sobolev_timeDerivative_hamiltonianOrdinarySourceFlow hs D φ hf time)
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp periodOneSobolevSynthesis
  have hx := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hy := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hfirst : (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2 : ℝ))) =
      (fun r => (A.hamiltonianOrdinaryPhysicalFlow D φ hf r).1 x) := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      _ (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf r)).1 x
  have hsecond : (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2 : ℝ))) =
      (fun r => (A.hamiltonianOrdinaryPhysicalFlow D φ hf r).2 x) := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      _ (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf r)).2 x
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2 : ℝ)))
    (periodOneSobolevSynthesis (deriv q time).1 (x : AddCircle (2 : ℝ))) time at hx
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2 : ℝ)))
    (periodOneSobolevSynthesis (deriv q time).2 (x : AddCircle (2 : ℝ))) time at hy
  rw [hfirst,congrFun hvel.1 x] at hx
  rw [hsecond,congrFun hvel.2 x] at hy
  exact ⟨hx,hy⟩

/-- The first physical component satisfies the scalar defocusing NLS
at every time and spatial point, with the Hamiltonian orientation. -/
theorem hasDerivAt_hamiltonianOrdinaryPhysicalFlow_scalarNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := fun r => (A.hamiltonianOrdinaryPhysicalFlow D φ hf r).1
    HasDerivAt (fun r => I*u r x)
      (-deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x) time := by
  dsimp only
  have hd := (A.hasDerivAt_hamiltonianOrdinaryPhysicalFlow hs D φ hf time x).1.const_mul I
  have he := sourceFiniteGapPhysicalNLSVectorField_scalar (by simp) (by norm_num)
    (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time) x
  change I*(classicalNLSVectorField (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1
    (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).2).1 x = _ at he
  rw [he] at hd
  exact hd

/-- The familiar pointwise equation `i u_t = -u_xx + 2 |u|² u`
for the actual constructed finite-gap physical trajectory. -/
theorem hamiltonianOrdinaryPhysicalFlow_scalarNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := fun r => (A.hamiltonianOrdinaryPhysicalFlow D φ hf r).1
    I*deriv (fun r => u r x) time = -deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x := by
  dsimp only
  have hd := (A.hasDerivAt_hamiltonianOrdinaryPhysicalFlow hs D φ hf time x).1
  have hscalar := A.hasDerivAt_hamiltonianOrdinaryPhysicalFlow_scalarNLS hs D φ hf time x
  rw [hd.deriv]
  exact (hd.const_mul I).unique hscalar

end SourceAbelianMomentAtlas

/-- Every real finite-gap Hilbert source has a global physical trajectory
with its exact initial Fourier representative, smooth periodic spatial
slices, and the pointwise scalar NLS equation. All spectral data are constructed. -/
theorem exists_sourceFiniteGap_pointwiseNLS_trajectory
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ u : ℝ → ℝ → ℂ,
      u 0 = (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 ∧
      ∀ time : ℝ, ContDiff ℝ ∞ (u time) ∧ Function.Periodic (u time) 1 ∧
        ∀ x : ℝ, DifferentiableAt ℝ (fun r => u r x) time ∧
          I*deriv (fun r => u r x) time =
            -deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  refine ⟨fun time => (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1,?_,?_⟩
  · exact congrArg Prod.fst (A.hamiltonianOrdinaryPhysicalFlow_zero D φ hf)
  · intro time
    have hreg := A.hamiltonianOrdinaryPhysicalFlow_regular D φ hf time
    refine ⟨hreg.1.1,hreg.2.1,?_⟩
    intro x
    exact ⟨(A.hasDerivAt_hamiltonianOrdinaryPhysicalFlow hs.toSourcePsiIsolatingComplexExtension
      D φ hf time x).1.differentiableAt,
      A.hamiltonianOrdinaryPhysicalFlow_scalarNLS hs.toSourcePsiIsolatingComplexExtension D φ hf time x⟩

end NLS.ZakharovShabat
