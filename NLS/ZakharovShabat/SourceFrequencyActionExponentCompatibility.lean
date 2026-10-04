import NLS.ZakharovShabat.SourceFrequencyActionSpaceMaps

/-! # Exponent-independent frequency values on summable actions

A nonnegative l1 action sequence has one real Hilbert source representative.
Including that source at two other exponents preserves the original actions
and the normalized frequency. Consequently independently constructed action
maps agree there, even with different source, action, and target exponents.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X : Set (CoeffPair p)}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A Hilbert source realizing a summable action sequence realizes the same
sequence after inclusion at any larger source exponent. -/
theorem actionSequence_hilbert_realization
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule 2) (b : RealCoeff 1)
    (hb : ∀ n, sourceComplexAction (by simp) (by norm_num) n φ.val = (b n : ℂ)) :
    sourceActionSequence (q := q) hp hp1 t (realTypeSourceExponentInclusion h2p φ).val =
      Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
  ext n
  exact (D.actionSequence_apply _ (D.real_subset (realTypeSourceExponentInclusion h2p φ).property) n).trans
    ((sourceComplexAction_real_exponent (by simp) hp (by norm_num) hp1 h2p n φ).symm.trans (hb n))

end SourceBirkhoffMapComplexData
namespace SourceAbelianMomentAtlas
variable {p' q' : ℝ≥0∞} [Fact (1 ≤ p')] [Fact (1 ≤ q')] [p'.HolderTriple p' q']
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {hp' : p' ≠ ⊤} {hp1' : 1 < p'}
  {W P : Set (CoeffPair p)} {W' P' : Set (CoeffPair p')}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {s' : (n : ℤ) → CoeffPair p' → DeletedCoeff p' n}
  {W₀ B X : Set (CoeffPair p)} {W₀' B' X' : Set (CoeffPair p')}
  {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {t' : (n : ℤ) → CoeffPair p' → DeletedCoeff p' n}

/-- Action maps recovering normalized frequencies agree on the entire
nonnegative summable cone, across independently chosen source exponents and atlases. -/
theorem actionMap_eq_on_nonnegative_summable
    (A : SourceAbelianMomentAtlas hp hp1 W s) (A' : SourceAbelianMomentAtlas hp' hp1' W' s')
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (hs' : SourcePsiIsolatingComplexExtension hp' hp1' P' s')
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t)
    (D' : SourceBirkhoffMapComplexData hp' hp1' W₀' B' X' t')
    (h2p : 2 ≤ p) (h2p' : 2 ≤ p')
    (F : Coeff q → ℤ → ℂ) (G : Coeff q' → ℤ → ℂ)
    (hF : ∀ ψ : realTypeSourceSubmodule p, ∀ n,
      F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val)
    (hG : ∀ ψ : realTypeSourceSubmodule p', ∀ n,
      G (sourceActionSequence (q := q') hp' hp1' t' ψ.val) n = A'.renormalizedFrequency n ψ.val)
    (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) (n : ℤ) :
    F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) n =
      G (Coeff.exponentInclusion (Fact.out : 1 ≤ q') (RealCoeff.complexCLM 1 b)) n := by
  obtain ⟨φ,hφ⟩ := exists_hilbertSource_of_nonnegative_actions b hb
  let ψ : realTypeSourceSubmodule p := realTypeSourceExponentInclusion h2p φ
  let ψ' : realTypeSourceSubmodule p' := realTypeSourceExponentInclusion h2p' φ
  have hi : sourceActionSequence (q := q) hp hp1 t ψ.val =
      Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) :=
    D.actionSequence_hilbert_realization h2p φ b hφ
  have hi' : sourceActionSequence (q := q') hp' hp1' t' ψ'.val =
      Coeff.exponentInclusion (Fact.out : 1 ≤ q') (RealCoeff.complexCLM 1 b) :=
    D'.actionSequence_hilbert_realization h2p' φ b hφ
  have hf := hF ψ n
  have hg := hG ψ' n
  rw [hi] at hf
  rw [hi'] at hg
  exact hf.trans ((A.renormalizedFrequency_real_eq_of_coefficients A' hs hs' ψ ψ'
    (fun _ => ⟨rfl,rfl⟩) n).trans hg.symm)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
