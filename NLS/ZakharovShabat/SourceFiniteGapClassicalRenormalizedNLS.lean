import NLS.ZakharovShabat.ClassicalRenormalizedNLSGauge
import NLS.ZakharovShabat.SourceFiniteGapClassicalNLS
import NLS.ZakharovShabat.SourceFiniteGapPointwiseRenormalizedNLS

/-! # Classical uniqueness and finite-gap solution agreement

The constructed spectral flow is a classical renormalized NLS trajectory in the uniform
function space. Hence every classical trajectory from the same finite-gap
initial representative agrees with this flow at all real times.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat
namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The first physical component as a trajectory of continuous circle functions. -/
def hamiltonianRenormalizedContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) : C(AddCircle (2 : ℝ), ℂ) :=
  periodOneSobolevSynthesis (sourceFiniteGapSobolevPair (by simp) (by norm_num)
    (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
    (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)).1

/-- The continuous representative is exactly the already constructed physical flow. -/
theorem hamiltonianRenormalizedContinuousFlow_coe
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    (fun x : ℝ => A.hamiltonianRenormalizedContinuousFlow D φ hf time (x : AddCircle (2 : ℝ))) =
      (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 :=
  (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) _ _).1

/-- The finite-gap flow is differentiable in the uniform norm. -/
theorem differentiable_hamiltonianRenormalizedContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Differentiable ℝ (A.hamiltonianRenormalizedContinuousFlow D φ hf) := by
  have hd := ((periodOneSobolevSynthesis.comp
    (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp
      (A.differentiable_hamiltonianRenormalizedSourceFlow_sobolev D φ hf)
  change Differentiable ℝ (A.hamiltonianRenormalizedContinuousFlow D φ hf) at hd
  exact hd

/-- The actual finite-gap Hamiltonian trajectory satisfies all hypotheses
of classical periodic renormalized NLS uniqueness. -/
theorem isClassicalRenormalizedNLSTrajectory_hamiltonianRenormalizedContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    IsClassicalRenormalizedNLSTrajectory (sourceOrdinaryMass le_rfl φ) (A.hamiltonianRenormalizedContinuousFlow D φ hf) := by
  have hd := A.differentiable_hamiltonianRenormalizedContinuousFlow D φ hf
  refine ⟨hd,?_,?_,?_⟩
  · intro time
    rw [A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time]
    exact (A.hamiltonianRenormalizedPhysicalFlow_regular D φ hf time).1.1
  · intro time
    rw [A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time]
    exact (A.hamiltonianRenormalizedPhysicalFlow_regular D φ hf time).2.1
  · intro time x
    have he := ((ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      time ((hd time).hasDerivAt)
    change HasDerivAt (fun r => A.hamiltonianRenormalizedContinuousFlow D φ hf r (x : AddCircle (2 : ℝ)))
      (deriv (A.hamiltonianRenormalizedContinuousFlow D φ hf) time (x : AddCircle (2 : ℝ))) time at he
    have heq : (fun r => A.hamiltonianRenormalizedContinuousFlow D φ hf r (x : AddCircle (2 : ℝ))) =
        (fun r => (A.hamiltonianRenormalizedPhysicalFlow D φ hf r).1 x) := by
      funext r
      exact congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf r) x
    rw [heq] at he
    have hvel := he.unique (A.hasDerivAt_hamiltonianRenormalizedPhysicalFlow hs D φ hf time x).1
    rw [hvel,A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time,scalarClassicalNLSVectorField_eq]
    have hreal : (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).2 =
        fun y => conj ((A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 y) :=
      funext (A.hamiltonianRenormalizedPhysicalFlow_real D φ hf time)
    rw [hreal,congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time) x]

/-- Any classical trajectory with the actual finite-gap initial representative
agrees with the constructed physical trajectory at every time and point. -/
theorem classicalRenormalizedNLS_eq_hamiltonianRenormalizedPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalRenormalizedNLSTrajectory (sourceOrdinaryMass le_rfl φ) u)
    (hinit : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x) (time x : ℝ) :
    u time (x : AddCircle (2 : ℝ)) = (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 x := by
  have hzero : u 0 = A.hamiltonianRenormalizedContinuousFlow D φ hf 0 := by
    ext y
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      rw [hinit]
      have he := congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf 0) y
      simpa only [A.hamiltonianRenormalizedPhysicalFlow_zero D φ hf] using he.symm
  have he := hu.eq_of_eq_at (A.isClassicalRenormalizedNLSTrajectory_hamiltonianRenormalizedContinuousFlow hs D φ hf) 0 hzero
  rw [he]
  exact congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time) x

/-- The actual renormalized physical flow is the positive mass gauge of
the ordinary physical flow. Classical uniqueness proves this identity
without assuming any gauge-equivariance property of the Birkhoff map. -/
theorem hamiltonianRenormalizedContinuousFlow_eq_gauge
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    A.hamiltonianRenormalizedContinuousFlow D φ hf =
      classicalNLSGauge (sourceOrdinaryMass le_rfl φ) (A.hamiltonianOrdinaryContinuousFlow D φ hf) := by
  apply (A.isClassicalRenormalizedNLSTrajectory_hamiltonianRenormalizedContinuousFlow hs D φ hf).eq_of_eq_at
    ((A.isClassicalNLSTrajectory_hamiltonianOrdinaryContinuousFlow hs D φ hf).gauge _) 0
  rw [classicalNLSGauge_zero_time]
  ext y
  induction y using QuotientAddGroup.induction_on with
  | H y =>
    have hr := congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf 0) y
    have ho := congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf 0) y
    rw [A.hamiltonianRenormalizedPhysicalFlow_zero] at hr
    rw [A.hamiltonianOrdinaryPhysicalFlow_zero] at ho
    exact hr.trans ho.symm

/-- Pointwise gauge agreement, with the exact physical sign and mass. -/
theorem hamiltonianRenormalizedPhysicalFlow_eq_gauge
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    (A.hamiltonianRenormalizedPhysicalFlow D φ hf time).1 x =
      Complex.exp (((4*sourceOrdinaryMass le_rfl φ*time : ℝ) : ℂ)*I)*
        (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 x := by
  have he := congrArg (fun u : ℝ → C(AddCircle (2 : ℝ), ℂ) => u time (x : AddCircle (2 : ℝ)))
    (A.hamiltonianRenormalizedContinuousFlow_eq_gauge hs D φ hf)
  change A.hamiltonianRenormalizedContinuousFlow D φ hf time (x : AddCircle (2 : ℝ)) =
    classicalNLSGaugePhase (sourceOrdinaryMass le_rfl φ) time *
      A.hamiltonianOrdinaryContinuousFlow D φ hf time (x : AddCircle (2 : ℝ)) at he
  rw [congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time) x,
    congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time) x] at he
  exact he

end SourceAbelianMomentAtlas

/-- Every actual real finite-gap Hilbert source admits exactly one classical
periodic renormalized NLS trajectory in the uniform-norm differentiable solution class.
The atlas and Birkhoff data are constructed internally. -/
theorem existsUnique_sourceFiniteGap_classicalRenormalizedNLS_trajectory
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ), IsClassicalRenormalizedNLSTrajectory (sourceOrdinaryMass le_rfl φ) u ∧
      ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  have hsi := hs.toSourcePsiIsolatingComplexExtension
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  refine ⟨A.hamiltonianRenormalizedContinuousFlow D φ hf,⟨
    A.isClassicalRenormalizedNLSTrajectory_hamiltonianRenormalizedContinuousFlow hsi D φ hf,?_⟩,?_⟩
  · intro x
    have he := congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf 0) x
    simpa only [A.hamiltonianRenormalizedPhysicalFlow_zero D φ hf] using he
  · intro u hu
    funext time
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      exact (A.classicalRenormalizedNLS_eq_hamiltonianRenormalizedPhysicalFlow hsi D φ hf u hu.1 hu.2 time x).trans
        (congrFun (A.hamiltonianRenormalizedContinuousFlow_coe D φ hf time) x).symm

end NLS.ZakharovShabat
