import NLS.ZakharovShabat.SourceFiniteGapPointwiseNLS
import NLS.ZakharovShabat.SourceRenormalizedMassCorrection

/-! # The renormalized finite-gap flow solves the physical PDE pointwise

The source velocity and the H¹ time lift identify both physical time
derivatives. The first component satisfies i u_t = -u_xx + 2 |u|² u - 4 M u
with the conserved initial physical mass M.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.Poisson
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The mass in the renormalized equation is the unit-period integral
of the squared modulus of the actual physical finite-gap representative. -/
theorem sourceOrdinaryMass_eq_finiteGap_integral
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceOrdinaryMass le_rfl φ = ∫ x in (0 : ℝ)..1,
      ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x‖^2 := by
  have hm : (sourceOrdinaryMass le_rfl φ : ℂ) =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 := by
    rw [sourceOrdinaryMass_complex,sourceOrdinaryComplexMass,sourceHilbertMass,
      reflectedHilbertPairing_apply,sourceFiniteGapNLSHamiltonian_one]
    rfl
  apply Complex.ofReal_injective
  rw [hm,sourceFiniteGapNLSHamiltonian,classicalNLSHamiltonian_one,
    ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [sourceFiniteGapPhysicalPair_real]
  simpa only [Complex.ofReal_pow] using Complex.mul_conj' ((sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x)

/-- Synthesis of the source mass correction has the exact two physical
component signs. Subtracting its H¹ representative reduces to ordinary NLS. -/
theorem periodOneSobolevSynthesis_eq_finiteGapRenormalizedNLS
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    c (v : ScalarDomain 2 × ScalarDomain 2)
    (hv : sobolevSourceInclusion v = sourceFiniteGapPhysicalNLSCoefficients φ hf +
      c • sourcePhase φ.val) :
    (fun x : ℝ => periodOneSobolevSynthesis v.1 (x : AddCircle (2 : ℝ))) =
      (fun x => (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1 x +
        c*I*(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x) ∧
    (fun x : ℝ => periodOneSobolevSynthesis v.2 (x : AddCircle (2 : ℝ))) =
      (fun x => (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2 x -
        c*I*(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 x) := by
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  let b : ScalarDomain 2 × ScalarDomain 2 := ((c*I) • a.1,-(c*I) • a.2)
  have hb : sobolevSourceInclusion b = c • sourcePhase φ.val := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n
    · have ha := congrArg (fun q : CoeffPair 2 => q.fst n)
        (sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf)
      change scalarInclusion a.1 n = φ.val.fst n at ha
      change scalarInclusion ((c*I) • a.1) n = (c • (I • φ.val.fst)) n
      simp only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,ha,mul_assoc]
    · have ha := congrArg (fun q : CoeffPair 2 => q.snd n)
        (sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf)
      change scalarInclusion a.2 n = φ.val.snd n at ha
      change scalarInclusion (-(c*I) • a.2) n = (c • (-I • φ.val.snd)) n
      simp only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,ha]
      ring
  have hh : sobolevSourceInclusion (v-b) = sourceFiniteGapPhysicalNLSCoefficients φ hf := by
    rw [map_sub,hv,hb,add_sub_cancel_right]
  have he := periodOneSobolevSynthesis_eq_finiteGapPhysicalNLS φ hf (v-b) hh
  have ha := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  constructor <;> funext x
  · have h := congrFun he.1 x
    change periodOneSobolevSynthesis (v.1-b.1) (x : AddCircle (2 : ℝ)) = _ at h
    simp only [map_sub,ContinuousMap.sub_apply,b,map_smul,ContinuousMap.smul_apply,smul_eq_mul] at h
    rw [show periodOneSobolevSynthesis a.1 (x : AddCircle (2 : ℝ)) = _ from congrFun ha.1 x] at h
    exact sub_eq_iff_eq_add.mp h
  · have h := congrFun he.2 x
    change periodOneSobolevSynthesis (v.2-b.2) (x : AddCircle (2 : ℝ)) = _ at h
    simp only [map_sub,ContinuousMap.sub_apply,b,map_smul,ContinuousMap.smul_apply,smul_eq_mul,neg_mul,sub_neg_eq_add] at h
    rw [show periodOneSobolevSynthesis a.2 (x : AddCircle (2 : ℝ)) = _ from congrFun ha.2 x] at h
    exact eq_sub_iff_add_eq.mpr h

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical pair of the constructed Hamiltonian-oriented finite-gap trajectory. -/
def hamiltonianRenormalizedPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  sourceFiniteGapPhysicalPair (by simp) (by norm_num)
    (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
    (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)

@[simp] theorem hamiltonianRenormalizedPhysicalFlow_zero
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    A.hamiltonianRenormalizedPhysicalFlow D φ hf 0 = sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf := by
  simp [hamiltonianRenormalizedPhysicalFlow]

/-- Both physical components stay smooth and period one in space. -/
theorem hamiltonianRenormalizedPhysicalFlow_regular
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    (ContDiff ℝ ∞ (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 ∧
      ContDiff ℝ ∞ (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).2) ∧
    (Function.Periodic (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 1 ∧
      Function.Periodic (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).2 1) :=
  ⟨contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _,
    periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _⟩

/-- The actual physical trajectory retains the conjugate-pair real form. -/
theorem hamiltonianRenormalizedPhysicalFlow_real
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).2 x =
      (starRingEnd ℂ) ((A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 x) :=
  sourceFiniteGapPhysicalPair_real (by simp) (by norm_num) _ _ x

/-- The actual physical mass is conserved on the renormalized trajectory. -/
theorem hamiltonianRenormalizedPhysicalFlow_mass
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖(A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 x‖^2) =
      sourceOrdinaryMass le_rfl φ := by
  rw [hamiltonianRenormalizedPhysicalFlow,← sourceOrdinaryMass_eq_finiteGap_integral,
    A.hamiltonianRenormalizedSourceFlow_mass]

/-- The H¹ time derivative has the physical renormalized NLS Fourier coefficients. -/
theorem sobolev_timeDerivative_hamiltonianRenormalizedSourceFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    sobolevSourceInclusion (deriv (fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ r)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf r)) time) =
      sourceFiniteGapPhysicalNLSCoefficients (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
        (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time) +
      (4*sourceOrdinaryMass le_rfl φ : ℂ) • sourcePhase (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time).val := by
  have hd := (A.differentiable_hamiltonianRenormalizedSourceFlow_sobolev D φ hf time).hasDerivAt
  have hi := (sobolevSourceInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  change HasDerivAt (fun r => sobolevSourceInclusion (sourceFiniteGapSobolevPair
    (by simp) (by norm_num) (A.hamiltonianRenormalizedSourceFlow D le_rfl φ r)
    (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf r))) _ time at hi
  simp only [sobolevSourceInclusion_sourceFiniteGapSobolevPair] at hi
  exact hi.unique (A.hasDerivAt_hamiltonianRenormalizedSourceFlow_physicalNLS hs D φ hf time)

/-- Both actual time derivatives equal the physical NLS field with the mass rotation. -/
theorem hasDerivAt_hamiltonianRenormalizedPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := A.hamiltonianRenormalizedPhysicalFlow D φ hf
    HasDerivAt (fun r => (u r).1 x) ((classicalNLSVectorField (u time).1 (u time).2).1 x +
        (4*sourceOrdinaryMass le_rfl φ : ℂ)*I*(u time).1 x) time ∧
    HasDerivAt (fun r => (u r).2 x) ((classicalNLSVectorField (u time).1 (u time).2).2 x -
        (4*sourceOrdinaryMass le_rfl φ : ℂ)*I*(u time).2 x) time := by
  dsimp only
  let q := fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num)
    (A.hamiltonianRenormalizedSourceFlow D le_rfl φ r)
    (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf r)
  have hd : HasDerivAt q (deriv q time) time :=
    (A.differentiable_hamiltonianRenormalizedSourceFlow_sobolev D φ hf time).hasDerivAt
  have hvel := periodOneSobolevSynthesis_eq_finiteGapRenormalizedNLS _ _ (4*sourceOrdinaryMass le_rfl φ : ℂ) (deriv q time)
    (A.sobolev_timeDerivative_hamiltonianRenormalizedSourceFlow hs D φ hf time)
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp periodOneSobolevSynthesis
  have hx := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hy := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hfirst : (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2 : ℝ))) =
      (fun r => (A.hamiltonianRenormalizedPhysicalFlow D φ hf r).1 x) := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      _ (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf r)).1 x
  have hsecond : (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2 : ℝ))) =
      (fun r => (A.hamiltonianRenormalizedPhysicalFlow D φ hf r).2 x) := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      _ (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf r)).2 x
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2 : ℝ)))
    (periodOneSobolevSynthesis (deriv q time).1 (x : AddCircle (2 : ℝ))) time at hx
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2 : ℝ)))
    (periodOneSobolevSynthesis (deriv q time).2 (x : AddCircle (2 : ℝ))) time at hy
  rw [hfirst,congrFun hvel.1 x] at hx
  rw [hsecond,congrFun hvel.2 x] at hy
  exact ⟨hx,hy⟩

/-- The first physical component satisfies the scalar renormalized defocusing NLS
at every time and spatial point, with the Hamiltonian orientation. -/
theorem hasDerivAt_hamiltonianRenormalizedPhysicalFlow_scalarNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := fun r => (A.hamiltonianRenormalizedPhysicalFlow D φ hf r).1
    HasDerivAt (fun r => I*u r x)
      (-deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x - (4*sourceOrdinaryMass le_rfl φ : ℂ)*u time x) time := by
  dsimp only
  have hd := (A.hasDerivAt_hamiltonianRenormalizedPhysicalFlow hs D φ hf time x).1.const_mul I
  have he := sourceFiniteGapPhysicalNLSVectorField_scalar (by simp) (by norm_num)
    (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
    (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time) x
  change I*(classicalNLSVectorField (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1
    (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).2).1 x = _ at he
  rw [mul_add,he] at hd
  have hc (m z : ℂ) : I*(m*I*z) = -m*z := by
    calc
      I*(m*I*z) = m*(I*I)*z := by ring
      _ = -m*z := by rw [I_mul_I]; ring
  simp only [hc,neg_mul,← sub_eq_add_neg] at hd
  exact hd

/-- The familiar pointwise equation `i u_t = -u_xx + 2 |u|² u - 4 M u`
for the actual constructed finite-gap physical trajectory. -/
theorem hamiltonianRenormalizedPhysicalFlow_scalarNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let u := fun r => (A.hamiltonianRenormalizedPhysicalFlow D φ hf r).1
    I*deriv (fun r => u r x) time = -deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x - (4*sourceOrdinaryMass le_rfl φ : ℂ)*u time x := by
  dsimp only
  have hd := (A.hasDerivAt_hamiltonianRenormalizedPhysicalFlow hs D φ hf time x).1
  have hscalar := A.hasDerivAt_hamiltonianRenormalizedPhysicalFlow_scalarNLS hs D φ hf time x
  rw [hd.deriv]
  exact (hd.const_mul I).unique hscalar

end SourceAbelianMomentAtlas

/-- Every real finite-gap Hilbert source has a global physical trajectory
with its exact initial Fourier representative, smooth periodic spatial
slices, and the pointwise renormalized NLS equation. All spectral data are constructed. -/
theorem exists_sourceFiniteGap_pointwiseRenormalizedNLS_trajectory
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ u : ℝ → ℝ → ℂ,
      u 0 = (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 ∧
      ∀ time : ℝ, ContDiff ℝ ∞ (u time) ∧ Function.Periodic (u time) 1 ∧
        ∀ x : ℝ, DifferentiableAt ℝ (fun r => u r x) time ∧
          I*deriv (fun r => u r x) time =
            -deriv (deriv (u time)) x+2*(‖u time x‖^2 : ℝ)*u time x - (4*sourceOrdinaryMass le_rfl φ : ℂ)*u time x := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  refine ⟨fun time => (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1,?_,?_⟩
  · exact congrArg Prod.fst (A.hamiltonianRenormalizedPhysicalFlow_zero D φ hf)
  · intro time
    have hreg := A.hamiltonianRenormalizedPhysicalFlow_regular D φ hf time
    refine ⟨hreg.1.1,hreg.2.1,?_⟩
    intro x
    exact ⟨(A.hasDerivAt_hamiltonianRenormalizedPhysicalFlow hs.toSourcePsiIsolatingComplexExtension
      D φ hf time x).1.differentiableAt,
      A.hamiltonianRenormalizedPhysicalFlow_scalarNLS hs.toSourcePsiIsolatingComplexExtension D φ hf time x⟩

end NLS.ZakharovShabat
