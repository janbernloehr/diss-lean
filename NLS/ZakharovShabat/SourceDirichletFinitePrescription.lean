import NLS.ZakharovShabat.SourceDirichletTerminalData
import NLS.ZakharovShabat.SourceDirichletSpectralTraversal

/-! # Prescribing finitely many actual Dirichlet terminals

The complete indexed spectral flows realize any finite collection of
admissible terminal pairs. Every unselected terminal is retained exactly,
and the resulting real Hilbert source has the original periodic spectrum
with all algebraic multiplicities.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceDirichletFinitePrescription_factTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- One prescribed terminal is realized while all other terminal pairs and the
entire periodic spectrum are preserved. -/
theorem exists_isospectral_source_with_terminal
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (z : ℂ × ℂ)
    (hz : z ∈ sourceDirichletSpectralSheet (by simp) (by norm_num) k φ.val) :
    ∃ ψ : realTypeSourceSubmodule 2,
      ψ ∈ sourceIsospectralSet (by simp) φ ∧
      sourceDirichletTerminalData (by simp) (by norm_num) ψ k = z ∧
      ∀ n : ℤ, n ≠ k → sourceDirichletTerminalData (by simp) (by norm_num) ψ n =
        sourceDirichletTerminalData (by simp) (by norm_num) φ n := by
  let φ₀ : realTypeSourceLocus 2 := ⟨φ.val,φ.property⟩
  obtain ⟨t,ht⟩ := exists_sourceDirichletSpectralFlow_terminal_eq k φ₀ z hz
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨(sourceDirichletSpectralFlow k φ₀ t).val,(sourceDirichletSpectralFlow k φ₀ t).property⟩
  refine ⟨ψ,?_,ht,?_⟩
  · apply (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ ψ).mpr
    exact funext (sourceDirichletSpectralFlow_conserved k φ₀ t).2
  · intro n hnk
    have he := other_dirichletTerminals_sourceDirichletSpectralGlobalCurve k n hnk φ₀ t
    exact Prod.ext he.1 he.2

/-- Any finite prescription of admissible terminal pairs is realized on the
actual isospectral set; every terminal outside the finite set stays fixed. -/
theorem exists_isospectral_source_with_finite_terminals
    (φ : realTypeSourceSubmodule 2) (z : ℤ → ℂ × ℂ)
    (hz : ∀ n, z n ∈ sourceDirichletSpectralSheet (by simp) (by norm_num) n φ.val)
    (s : Finset ℤ) :
    ∃ ψ : realTypeSourceSubmodule 2,
      ψ ∈ sourceIsospectralSet (by simp) φ ∧
      (∀ n ∈ s, sourceDirichletTerminalData (by simp) (by norm_num) ψ n = z n) ∧
      ∀ n ∉ s, sourceDirichletTerminalData (by simp) (by norm_num) ψ n =
        sourceDirichletTerminalData (by simp) (by norm_num) φ n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨φ,⟨rfl,fun _ => rfl⟩,by simp,by simp⟩
  | @insert k s hks ih =>
    obtain ⟨ψ,hψ,hfinite,houtside⟩ := ih
    have hzk : z k ∈ sourceDirichletSpectralSheet (by simp) (by norm_num) k ψ.val := by
      rw [sourceDirichletSpectralSheet_eq_of_isospectral (by simp) (by norm_num) φ ψ hψ k]
      exact hz k
    obtain ⟨χ,hχ,hk,hother⟩ := exists_isospectral_source_with_terminal ψ k (z k) hzk
    refine ⟨χ,⟨hχ.1.trans hψ.1,fun w => (hχ.2 w).trans (hψ.2 w)⟩,?_,?_⟩
    · intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hk
      · exact (hother n (fun he => hks (he ▸ hn))).trans (hfinite n hn)
    · intro n hn
      have hnk : n ≠ k := fun he => hn (Finset.mem_insert.mpr (Or.inl he))
      have hns : n ∉ s := fun hs => hn (Finset.mem_insert.mpr (Or.inr hs))
      exact (hother n hnk).trans (houtside n hns)

end NLS.ZakharovShabat
