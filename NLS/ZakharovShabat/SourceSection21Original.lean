import NLS.ZakharovShabat.SourceSection21Hamiltonian
import NLS.ZakharovShabat.SourceSection21SignCorrections

/-! # Section 21 for one original Birkhoff family

The moment construction works at every finite exponent above one. At
exponent four, one original family carries the same primitive-power
moments, cubic Hamiltonian, action gradient, and local concavity. All
auxiliary packages are constructed before the source or moment index.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct the complete moment package after the original Sections 17–20. -/
theorem sourceSection21_original_moments (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s,
    ∃ D : SourceSection17OriginalData hp hp1 W₀ W V s,
    ∃ Wa : Set (CoeffPair p), ∃ A : SourceAbelianMomentAtlas hp hp1 Wa s,
    ∃ B U : Set (CoeffPair p), ∃ Q : SourceSection20Data D A B U,
    ∃ Wp : Set (CoeffPair p), ∃ P : SourcePrimitivePowerAtlas hp hp1 Wp,
    ∃ T : Set (CoeffPair p), SourceSection21MomentData Q P T := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original hp hp1
  obtain ⟨Wp,P,T,M⟩ := Q.exists_section21_moments
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,Wp,P,T,M⟩

local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- Retain any original Section 20 family and construct its Section 21
Hamiltonian package, including the already proved action concavity data. -/
theorem SourceSection20Data.exists_section21_hamiltonian
    {W₀ W V Wa B U : Set (CoeffPair 4)}
    {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection20Data D A B U) :
    ∃ Wp : Set (CoeffPair 4), ∃ P : SourcePrimitivePowerAtlas (by simp) (by norm_num) Wp,
    ∃ L : Set (Coeff 2), ∃ F : Coeff 2 → Coeff 2, ∃ H : Coeff 2 → ℂ,
    ∃ E : SourceOriginalHamiltonianData D L F H,
    ∃ T : Set (CoeffPair 4), SourceSection21HamiltonianData Q P E T := by
  obtain ⟨Wp,P,T,M⟩ := Q.exists_section21_moments
  obtain ⟨L₀,F,G⟩ := D.exists_frequency_asymptotic (q := 2) (by norm_num)
  obtain ⟨L,H,_,E⟩ := G.exists_original_hamiltonian
  obtain ⟨S,K,_⟩ := M.exists_hamiltonian_domain E
  exact ⟨Wp,P,L,F,H,E,S,K⟩

/-- One unconditional original construction supplies the full Section 21
source and action Hamiltonians with the same retained Section 20 frequency. -/
theorem sourceSection21_original :
    ∃ W₀ W V : Set (CoeffPair 4), ∃ s,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ Wa : Set (CoeffPair 4), ∃ A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s,
    ∃ B U : Set (CoeffPair 4), ∃ Q : SourceSection20Data D A B U,
    ∃ Wp : Set (CoeffPair 4), ∃ P : SourcePrimitivePowerAtlas (by simp) (by norm_num) Wp,
    ∃ L : Set (Coeff 2), ∃ F : Coeff 2 → Coeff 2, ∃ H : Coeff 2 → ℂ,
    ∃ E : SourceOriginalHamiltonianData D L F H,
    ∃ T : Set (CoeffPair 4), SourceSection21HamiltonianData Q P E T := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 4) (by simp) (by norm_num)
  obtain ⟨Wp,P,L,F,H,E,T,M⟩ := Q.exists_section21_hamiltonian
  exact ⟨W₀,W,V,s,D,Wa,A,B,U,Q,Wp,P,L,F,H,E,T,M⟩

end NLS.ZakharovShabat
