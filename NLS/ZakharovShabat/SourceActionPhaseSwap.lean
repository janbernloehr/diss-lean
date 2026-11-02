import NLS.ZakharovShabat.SourceFiniteActionSwap
import NLS.ZakharovShabat.SourceFiniteActionODEUniqueness
import NLS.ZakharovShabat.SourceComponentSwapRealTopology
import NLS.ZakharovShabat.SourceFiniteGapDensity

/-! # Actual source-flow covariance from Hamiltonian component exchange

The anti-Poisson swap and reflected frequency sign transport the finite
action ODE. Uniqueness in the actual Birkhoff coordinates identifies the
swapped source curve. Actual finite-gap density then proves covariance
on the entire Hilbert real source, without an angle identity assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Reflected physical frequencies give covariance of actual finite-support
source trajectories, via their original Hamiltonian ODE. -/
theorem imageFlow_componentSwap_of_support (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (hF : ∀ φ : realTypeSourceSubmodule p, ∀ n : ℤ,
      F.frequency (realSourceComponentSwap φ) n = -F.frequency φ (-n))
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s φ.val).2 n = 0) (τ : ℝ) :
    realSourceComponentSwap (F.imageFlow D φ τ) =
      F.imageFlow D (realSourceComponentSwap φ) τ := by
  let γ := fun r : ℝ => realSourceComponentSwap (F.imageFlow D φ r)
  have hd (r : ℝ) : HasDerivAt (fun σ => (γ σ).val)
      (sourceFiniteActionHamiltonianVector hp hp1 h2p (F.frequency (realSourceComponentSwap φ))
        (S.image Neg.neg) (γ r).val) r := by
    have he := ((sourceComponentSwap (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r
      (F.hasDerivAt_imageFlow_finiteAction D hp2 h2p φ S hz r)
    change HasDerivAt (fun σ => (γ σ).val)
      (sourceComponentSwap (sourceFiniteActionHamiltonianVector hp hp1 h2p (F.frequency φ) S
        (F.imageFlow D φ r).val)) r at he
    rw [sourceFiniteActionHamiltonianVector_componentSwap hp hp1 h2p _ _ _ (hF φ) S] at he
    exact he
  have hs (r : ℝ) : ∀ n ∉ S.image Neg.neg,
      (sourceComplexBirkhoffMap hp hp1 s (γ r).val).1 n = 0 ∧
      (sourceComplexBirkhoffMap hp hp1 s (γ r).val).2 n = 0 :=
    D.complex_support_componentSwap (F.imageFlow D φ r) S
      (F.complex_support_imageFlow D φ S hz r (F.mem_imageDomain_of_le_two D hp2 φ r))
  have he := D.complex_map_eq_phase_of_finiteAction_ode h2p
    (F.frequency (realSourceComponentSwap φ)) (S.image Neg.neg) γ hd hs τ
  have hzero : γ 0 = realSourceComponentSwap φ := by simp [γ]
  rw [hzero] at he
  apply D.complex_map_real_injective
  exact he.trans (F.complex_map_imageFlow D (realSourceComponentSwap φ) τ
    (F.mem_imageDomain_of_le_two D hp2 _ τ)).symm

/-- Actual finite-gap approximation extends covariance to every original
real Hilbert source, including infinitely many open gaps. -/
theorem imageFlow_componentSwap (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (hF : ∀ φ : realTypeSourceSubmodule p, ∀ n : ℤ,
      F.frequency (realSourceComponentSwap φ) n = -F.frequency φ (-n))
    (φ : realTypeSourceSubmodule p) (τ : ℝ) :
    realSourceComponentSwap (F.imageFlow D φ τ) =
      F.imageFlow D (realSourceComponentSwap φ) τ := by
  have hflow : Continuous (fun ψ : realTypeSourceSubmodule p => F.imageFlow D ψ τ) :=
    (F.continuous_imageFlow_of_le_two D hp2).comp
      (f := fun ψ : realTypeSourceSubmodule p => (τ,ψ)) (continuous_const.prodMk continuous_id)
  have hclosed : IsClosed {ψ : realTypeSourceSubmodule p |
      realSourceComponentSwap (F.imageFlow D ψ τ) = F.imageFlow D (realSourceComponentSwap ψ) τ} :=
    isClosed_eq (continuous_realSourceComponentSwap.comp hflow)
      (hflow.comp continuous_realSourceComponentSwap)
  have hsubset : sourceFiniteGapLocus hp hp1 ⊆ {ψ : realTypeSourceSubmodule p |
      realSourceComponentSwap (F.imageFlow D ψ τ) = F.imageFlow D (realSourceComponentSwap ψ) τ} := by
    intro ψ hψ
    obtain ⟨S,hS⟩ := D.exists_complex_support_finiteGap ψ hψ
    exact F.imageFlow_componentSwap_of_support D hp2 h2p hF ψ S hS τ
  exact (closure_minimal hsubset hclosed) ((dense_sourceFiniteGapLocus hp hp1) φ)

/-- The actual equal-field source diagonal is preserved by the lifted flow
whenever its frequency family has the reflected covariance. -/
theorem imageFlow_preserves_diagonal (F : SourceActionFrequency hp hp1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (hp2 : p ≤ 2) (h2p : 2 ≤ p)
    (hF : ∀ φ : realTypeSourceSubmodule p, ∀ n : ℤ,
      F.frequency (realSourceComponentSwap φ) n = -F.frequency φ (-n))
    (φ : realTypeSourceSubmodule p) (hφ : φ.val.fst = φ.val.snd) (τ : ℝ) :
    (F.imageFlow D φ τ).val.fst = (F.imageFlow D φ τ).val.snd := by
  apply (sourceComponentSwap_eq_self_iff _).mp
  have hs : realSourceComponentSwap φ = φ := Subtype.ext ((sourceComponentSwap_eq_self_iff _).mpr hφ)
  exact congrArg Subtype.val ((F.imageFlow_componentSwap D hp2 h2p hF φ τ).trans (congrArg (fun ψ => F.imageFlow D ψ τ) hs))

end NLS.ZakharovShabat.SourceActionFrequency
