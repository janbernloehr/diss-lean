import NLS.ZakharovShabat.ClassicalNLSUniqueness
import NLS.ZakharovShabat.SourceFiniteGapPointwiseNLS

/-! # Classical uniqueness and finite-gap solution agreement

The constructed spectral flow is a classical NLS trajectory in the uniform
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
def hamiltonianOrdinaryContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) : C(AddCircle (2 : ℝ), ℂ) :=
  periodOneSobolevSynthesis (sourceFiniteGapSobolevPair (by simp) (by norm_num)
    (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1

/-- The continuous representative is exactly the already constructed physical flow. -/
theorem hamiltonianOrdinaryContinuousFlow_coe
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    (fun x : ℝ => A.hamiltonianOrdinaryContinuousFlow D φ hf time (x : AddCircle (2 : ℝ))) =
      (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 :=
  (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) _ _).1

/-- The finite-gap flow is differentiable in the uniform norm. -/
theorem differentiable_hamiltonianOrdinaryContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Differentiable ℝ (A.hamiltonianOrdinaryContinuousFlow D φ hf) := by
  have hd := ((periodOneSobolevSynthesis.comp
    (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).differentiable.comp
      (A.differentiable_hamiltonianOrdinarySourceFlow_sobolev D φ hf)
  change Differentiable ℝ (A.hamiltonianOrdinaryContinuousFlow D φ hf) at hd
  exact hd

/-- The actual finite-gap Hamiltonian trajectory satisfies all hypotheses
of classical periodic NLS uniqueness. -/
theorem isClassicalNLSTrajectory_hamiltonianOrdinaryContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    IsClassicalNLSTrajectory (A.hamiltonianOrdinaryContinuousFlow D φ hf) := by
  have hd := A.differentiable_hamiltonianOrdinaryContinuousFlow D φ hf
  refine ⟨hd,?_,?_,?_⟩
  · intro time
    rw [A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time]
    exact (A.hamiltonianOrdinaryPhysicalFlow_regular D φ hf time).1.1
  · intro time
    rw [A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time]
    exact (A.hamiltonianOrdinaryPhysicalFlow_regular D φ hf time).2.1
  · intro time x
    have he := ((ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      time ((hd time).hasDerivAt)
    change HasDerivAt (fun r => A.hamiltonianOrdinaryContinuousFlow D φ hf r (x : AddCircle (2 : ℝ)))
      (deriv (A.hamiltonianOrdinaryContinuousFlow D φ hf) time (x : AddCircle (2 : ℝ))) time at he
    have heq : (fun r => A.hamiltonianOrdinaryContinuousFlow D φ hf r (x : AddCircle (2 : ℝ))) =
        (fun r => (A.hamiltonianOrdinaryPhysicalFlow D φ hf r).1 x) := by
      funext r
      exact congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf r) x
    rw [heq] at he
    have hvel := he.unique (A.hasDerivAt_hamiltonianOrdinaryPhysicalFlow hs D φ hf time x).1
    rw [hvel,A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time,scalarClassicalNLSVectorField_eq]
    have hreal : (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).2 =
        fun y => conj ((A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 y) :=
      funext (A.hamiltonianOrdinaryPhysicalFlow_real D φ hf time)
    rw [hreal]

/-- Any classical trajectory with the actual finite-gap initial representative
agrees with the constructed physical trajectory at every time and point. -/
theorem classicalNLS_eq_hamiltonianOrdinaryPhysicalFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) (hu : IsClassicalNLSTrajectory u)
    (hinit : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x) (time x : ℝ) :
    u time (x : AddCircle (2 : ℝ)) = (A.hamiltonianOrdinaryPhysicalFlow D φ hf time).1 x := by
  have hzero : u 0 = A.hamiltonianOrdinaryContinuousFlow D φ hf 0 := by
    ext y
    induction y using QuotientAddGroup.induction_on with
    | H y =>
      rw [hinit]
      have he := congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf 0) y
      simpa only [A.hamiltonianOrdinaryPhysicalFlow_zero D φ hf] using he.symm
  have he := hu.eq_of_eq_at (A.isClassicalNLSTrajectory_hamiltonianOrdinaryContinuousFlow hs D φ hf) 0 hzero
  rw [he]
  exact congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time) x

end SourceAbelianMomentAtlas

/-- Every actual real finite-gap Hilbert source admits exactly one classical
periodic NLS trajectory in the uniform-norm differentiable solution class.
The atlas and Birkhoff data are constructed internally. -/
theorem existsUnique_sourceFiniteGap_classicalNLS_trajectory
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ), IsClassicalNLSTrajectory u ∧
      ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  have hsi := hs.toSourcePsiIsolatingComplexExtension
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  refine ⟨A.hamiltonianOrdinaryContinuousFlow D φ hf,⟨
    A.isClassicalNLSTrajectory_hamiltonianOrdinaryContinuousFlow hsi D φ hf,?_⟩,?_⟩
  · intro x
    have he := congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf 0) x
    simpa only [A.hamiltonianOrdinaryPhysicalFlow_zero D φ hf] using he
  · intro u hu
    funext time
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      exact (A.classicalNLS_eq_hamiltonianOrdinaryPhysicalFlow hsi D φ hf u hu.1 hu.2 time x).trans
        (congrFun (A.hamiltonianOrdinaryContinuousFlow_coe D φ hf time) x).symm

end NLS.ZakharovShabat
