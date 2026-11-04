import NLS.ZakharovShabat.SourceFiniteGapFrequencyExponent
import NLS.ZakharovShabat.SourceComplexBirkhoffMap

/-! # Nonzero signed Birkhoff modes outside L²

Finite support of just the first complex Birkhoff component forces actual
spectral finite-gap regularity, hence square-summability of both original
source components. In particular a source outside L² has a nonzero first
Birkhoff coordinate at a signed index different from zero. This excludes
the zero-index degeneracy in mass-dependent phase obstructions.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Finite support of the first complex component forces actual finite-gap
regularity; finite Fourier support of the input is not assumed. -/
theorem finiteGap_of_complex_fst_vanishes_off
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hS : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0) :
    φ ∈ sourceFiniteGapLocus hp hp1 := by
  apply S.finite_toSet.subset
  intro n hn
  by_contra hnot
  have ha : sourceComplexAction hp hp1 n φ.val = 0 := by
    rw [← D.complex_map_action φ.val (D.real_subset φ.property) n,hS n hnot,zero_mul]
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property] at ha
  have hg := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n).2.2.mp ha
  exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)

/-- The original raw components are square summable whenever the first
complex Birkhoff sequence has finite support. -/
theorem mem_hilbert_of_complex_fst_vanishes_off
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hS : ∀ n ∉ S, (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n = 0) :
    Memℓp (fun n : ℤ => φ.val.fst n) 2 ∧ Memℓp (fun n : ℤ => φ.val.snd n) 2 := by
  have hf := D.finiteGap_of_complex_fst_vanishes_off φ S hS
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  have he₁ : (fun n : ℤ => ψ.val.fst n) = fun n => φ.val.fst n :=
    funext fun n => (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf n).1
  have he₂ : (fun n : ℤ => ψ.val.snd n) = fun n => φ.val.snd n :=
    funext fun n => (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf n).2
  exact ⟨he₁ ▸ lp.memℓp ψ.val.fst,he₂ ▸ lp.memℓp ψ.val.snd⟩

/-- A source outside the physical Hilbert domain has a nonzero signed mode
at n≠0. The mass-dependent phase therefore has a nonzero coefficient. -/
theorem exists_nonzero_complex_birkhoff_index
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (hφ : ¬ Memℓp (fun n : ℤ => φ.val.fst n) 2) :
    ∃ n : ℤ, n ≠ 0 ∧ (sourceComplexBirkhoffMap hp hp1 s φ.val).1 n ≠ 0 := by
  classical
  by_contra! h
  apply hφ
  exact (D.mem_hilbert_of_complex_fst_vanishes_off φ {0} (fun n hn =>
    h n (by simpa only [Finset.mem_singleton] using hn))).1

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
