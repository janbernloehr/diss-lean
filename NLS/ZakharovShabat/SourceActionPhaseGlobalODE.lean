import NLS.ZakharovShabat.SourceActionPhaseFlow
import NLS.ZakharovShabat.SourceFiniteGapHamiltonianODE

/-! # Actual finite-action ODEs for arbitrary action-invariant phase families

At exponents at most two the actual Birkhoff image is the whole target.
Finite coordinate support permits differentiation in the full source norm;
the injective Birkhoff differential identifies the original Hamiltonian field.
No particular hierarchy frequency or physical PDE is assumed here.
-/
noncomputable section
set_option autoImplicit false
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
namespace SourceActionFrequency
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual image condition is automatic in the proven global range. -/
theorem mem_imageDomain_of_le_two (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) : (τ,φ) ∈ F.imageDomain D :=
  D.proposition17_3 hp2 _

/-- The actual image inverse agrees with the established global inverse. -/
theorem imageFlow_eq_globalInverse (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    F.imageFlow D φ τ = (D.realHomeomorph hp2).symm (Birkhoff.decodeReal (F.phaseTrajectory D φ τ)) := by
  apply D.proposition17_2
  exact (D.real_map_realImageInverse _ (F.mem_imageDomain_of_le_two D hp2 φ τ)).trans
    ((D.realHomeomorph hp2).apply_symm_apply _).symm

/-- Joint source-norm continuity holds globally in the proven global range. -/
theorem continuous_imageFlow_of_le_two (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2) :
    Continuous (fun x : ℝ × realTypeSourceSubmodule p => F.imageFlow D x.2 x.1) := by
  have he : F.imageDomain D = univ := Set.eq_univ_of_forall fun x =>
    F.mem_imageDomain_of_le_two D hp2 x.2 x.1
  have hc := F.continuousOn_imageFlow D
  rw [he] at hc
  exact continuousOn_univ.mp hc

/-- The active original complex coordinates stay in their initial finite cutoff. -/
theorem complex_support_imageFlow (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0)
    (τ : ℝ) (hτ : (τ,φ) ∈ F.imageDomain D) :
    ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s (F.imageFlow D φ τ).val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s (F.imageFlow D φ τ).val).2 n = 0 := by
  intro n hn
  rw [F.complex_map_imageFlow D φ τ hτ]
  simp only [phaseTrajectory,Birkhoff.hamiltonianPhaseFlow_fst,Birkhoff.hamiltonianPhaseFlow_snd,
    (hz n hn).1,(hz n hn).2,mul_zero,and_self]

/-- Differentiation of the actual inverse lift in the full source norm. -/
theorem hasDerivAt_imageFlow_of_support (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (F.imageFlow D φ)
      ((D.realJacobianEquivAll (F.imageFlow D φ τ)).symm
        (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity (F.frequency φ) S
          (F.phaseTrajectory D φ τ)))) τ := by
  have hd := Birkhoff.hasDerivAt_hamiltonianPhaseFlow_of_support
    (F.frequency φ) S (sourceComplexBirkhoffMap hp hp1 s φ.val) hz τ
  have hr := (Birkhoff.decodeReal (p := p)).hasFDerivAt.comp_hasDerivAt τ hd
  have hi := (D.realHomeomorph_symm_hasStrictFDerivAt hp2
    (Birkhoff.decodeReal (F.phaseTrajectory D φ τ))).hasFDerivAt.comp_hasDerivAt τ hr
  change HasDerivAt (fun σ => (D.realHomeomorph hp2).symm (Birkhoff.decodeReal (F.phaseTrajectory D φ σ)))
    ((D.realJacobianEquivAll ((D.realHomeomorph hp2).symm (Birkhoff.decodeReal (F.phaseTrajectory D φ τ)))).symm
      (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity (F.frequency φ) S
        (F.phaseTrajectory D φ τ)))) τ at hi
  simpa only [← F.imageFlow_eq_globalInverse D hp2 φ] using! hi

/-- The derivative is the actual finite sum of original action fields,
with the exact Hamiltonian time orientation and initial frequencies. -/
theorem hasDerivAt_imageFlow_finiteAction (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0) (τ : ℝ) :
    HasDerivAt (fun σ => (F.imageFlow D φ σ).val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p (F.frequency φ) S (F.imageFlow D φ τ).val) τ := by
  let γ := F.imageFlow D φ
  let v := (D.realJacobianEquivAll (γ τ)).symm
    (Birkhoff.decodeReal (Birkhoff.finiteHamiltonianPhaseVelocity (F.frequency φ) S
      (F.phaseTrajectory D φ τ)))
  have ht : HasDerivAt γ v τ := F.hasDerivAt_imageFlow_of_support D hp2 φ S hz τ
  have hi := (realTypeSourceSubmodule p).subtypeL.hasFDerivAt.comp_hasDerivAt τ ht
  change HasDerivAt (fun σ => (γ σ).val) v.val τ at hi
  have hc := ((D.complex_map_analytic (γ τ).val (D.real_subset (γ τ).property)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt τ hi
  have he (σ : ℝ) : sourceComplexBirkhoffMap hp hp1 s (γ σ).val = F.phaseTrajectory D φ σ :=
    F.complex_map_imageFlow D φ σ (F.mem_imageDomain_of_le_two D hp2 φ σ)
  have hc' : HasDerivAt (fun σ => F.phaseTrajectory D φ σ)
      ((fderiv ℂ (sourceComplexBirkhoffMap hp hp1 s) (γ τ).val) v.val) τ := by
    simpa only [Function.comp_def,he] using! hc
  have hv := hc'.unique (Birkhoff.hasDerivAt_hamiltonianPhaseFlow_of_support
    (F.frequency φ) S (sourceComplexBirkhoffMap hp hp1 s φ.val) hz τ)
  have heq : v.val = sourceFiniteActionHamiltonianVector hp hp1 h2p (F.frequency φ) S (γ τ).val := by
    apply D.complex_jacobian_injective (γ τ)
    rw [hv,D.complex_jacobian_finiteActionHamiltonian,he τ]
    rfl
  simpa only [heq] using! hi

end SourceActionFrequency
end NLS.ZakharovShabat
