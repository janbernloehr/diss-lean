import NLS.ZakharovShabat.SourceHamiltonianRealActionBalls
import NLS.SequenceSpaces.RealActionBallGluing
import NLS.ZakharovShabat.SourcePositiveActionRealization
import NLS.ZakharovShabat.SourceFrequencyOrigin

/-! # Analytic Hamiltonian extension to ℓ² actions

The local factors glue on one open action domain containing every real
FL⁴ source action and the nonnegative ℓ¹ cone. The extension is real and
nonpositive on all nonnegative actions in its domain, and vanishes there
exactly at zero. Its source normalization is the cubic-moment Hamiltonian.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W : Set (CoeffPair 4)}
variable (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)

/-- The cubic-moment Hamiltonian has a unique analytic action extension
on an actual open ℓ² domain, with full nonnegative-domain sign and zero criterion. -/
theorem exists_hamiltonian_action_extension :
    ∃ W₀ B X : Set (CoeffPair 4), ∃ t : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n,
      ∃ _D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t,
      ∃ V : Set (Coeff 2), ∃ H : Coeff 2 → ℂ, IsOpen V ∧
        (∀ φ : realTypeSourceSubmodule 4, sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val ∈ V) ∧
        (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
          Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) (RealCoeff.complexCLM 1 b) ∈ V) ∧
        (∀ b ∈ V, ∃ ψ ∈ X, sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ = b) ∧
        (∀ b ∈ V, b ∈ Coeff.nonnegativeLocus 2 → ∃ ψ : realTypeSourceSubmodule 4,
          sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val = b) ∧
        AnalyticOnNhd ℂ H V ∧
        (∀ φ : realTypeSourceSubmodule 4,
          H (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) = A.renormalizedHamiltonian φ.val) ∧
        (∀ b ∈ V, b ∈ Coeff.nonnegativeLocus 2 →
          (H b).re ≤ 0 ∧ (H b).im = 0 ∧ (H b = 0 ↔ b = 0)) ∧
        (∀ G : Coeff 2 → ℂ, AnalyticOnNhd ℂ G V →
          (∀ φ : realTypeSourceSubmodule 4,
            G (sourceActionSequence (q := 2) (by simp) (by norm_num) t φ.val) = A.renormalizedHamiltonian φ.val) →
          EqOn G H V) := by
  classical
  obtain ⟨W₀,B,X,t,D,hballs⟩ := A.exists_hamiltonian_realActionBalls
  choose R hR hcomplex hreal hlocal using hballs
  let a : realTypeSourceSubmodule 4 → Coeff 2 := fun φ =>
    sourceActionSequence (by simp) (by norm_num) t φ.val
  let V := ⋃ φ, ball (a φ) (R φ)
  have ha (φ : realTypeSourceSubmodule 4) : a φ ∈ Coeff.nonnegativeLocus 2 :=
    D.actionSequence_mem_nonnegativeLocus φ
  have hcenter (φ : realTypeSourceSubmodule 4) : a φ ∈ V :=
    mem_iUnion.mpr ⟨φ,mem_ball_self (hR φ)⟩
  obtain ⟨H,hH,hrec⟩ := Coeff.exists_analytic_gluing_of_real_action_ball_recovery
    (by simp : (4:ℝ≥0∞) ≠ ⊤) a R (fun φ => A.renormalizedHamiltonian φ.val) ha hR hreal hlocal
  have hrealV : ∀ b ∈ V, b ∈ Coeff.nonnegativeLocus 2 → ∃ ψ, a ψ = b := by
    intro b hb hpos
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    exact hreal φ b hφ hpos
  refine ⟨W₀,B,X,t,D,V,H,isOpen_iUnion (fun _ => isOpen_ball),hcenter,?_,?_,hrealV,hH,hrec,?_,?_⟩
  · intro b hb
    obtain ⟨φ,hφ⟩ := exists_source_of_nonnegative_actions
      (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num) (by norm_num) b hb
    have he : a φ = Coeff.exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) (RealCoeff.complexCLM 1 b) := by
      ext n
      exact (D.actionSequence_apply φ.val (D.real_subset φ.property) n).trans (hφ n)
    rw [← he]
    exact hcenter φ
  · intro b hb
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    exact hcomplex φ b hφ
  · intro b hb hpos
    obtain ⟨ψ,hψ⟩ := hrealV b hb hpos
    have he : H b = A.renormalizedHamiltonian ψ.val := hψ ▸ hrec ψ
    obtain ⟨hle,him⟩ := A.real_renormalizedHamiltonian_nonpos ψ
    refine ⟨he ▸ hle,he ▸ him,?_⟩
    constructor
    · intro hz
      have hzero := (A.real_renormalizedHamiltonian_eq_zero_iff ψ).mp (he.symm.trans hz)
      subst ψ
      exact hψ.symm.trans D.actionSequence_zero
    · intro hz
      have hzero : a 0 = 0 := D.actionSequence_zero
      rw [hz,← hzero,hrec]
      exact (A.real_renormalizedHamiltonian_eq_zero_iff 0).mpr rfl
  · intro G hG hGrec
    exact Coeff.eqOn_of_real_action_ball_agreement (by simp : (4:ℝ≥0∞) ≠ ⊤) a R ha hR hreal G H hG hH
      (fun φ => (hGrec φ).trans (hrec φ).symm)

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
