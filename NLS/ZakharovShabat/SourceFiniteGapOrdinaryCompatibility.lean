import NLS.ZakharovShabat.SourceFiniteGapOrdinaryTrajectory
import NLS.ZakharovShabat.SourceComplexBirkhoffExponent
import NLS.ZakharovShabat.SourceOrdinaryFlow

/-! # Hilbert representatives of ordinary finite-gap dynamics

The coefficient-preserving Hilbert model recovers the original finite-gap
source under inclusion. Its ordinary flow has the same scalar Birkhoff
trajectory, even when observed in any larger finite exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p}

namespace SourceAbelianMomentAtlas
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₂ P₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {V₂ B₂ X₂ : Set (CoeffPair 2)} {t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The finite-gap physical frequency is the ordinary frequency of its Hilbert model. -/
theorem finiteGapOrdinaryFrequency_hilbertModel (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    A.finiteGapOrdinaryFrequency φ hf n =
      H.ordinaryPhaseFrequency le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) n := by
  rw [← H.finiteGapOrdinaryFrequency_eq_ordinary le_rfl _
    (sourceFiniteGapHilbertModel_mem hp hp1 φ hf)]
  apply Complex.ofReal_injective
  rw [A.finiteGapOrdinaryFrequency_physical hs E,H.finiteGapOrdinaryFrequency_physical hs₂ E,
    E.finiteGapFrequencyAtExponent_two]
  rfl

/-- Observing the included Hilbert flow gives the original finite-gap first coordinate. -/
theorem complex_map_hilbertOrdinaryFlow_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    {V B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {Vq Bq Xq : Set (CoeffPair q)}
    {tq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (Q : SourceBirkhoffMapComplexData hq hq1 Vq Bq Xq tq)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (n : ℤ) (τ : Icc (0 : ℝ) T) :
    (sourceComplexBirkhoffMap hq hq1 tq
      (realTypeSourceExponentInclusion h2q
        (H.ordinarySourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) τ.val)).val).1 n =
      A.finiteGapOrdinaryCoordinate t T φ hf n τ := by
  rw [← E.complex_map_exponent Q h2q,H.complex_map_ordinarySourceFlow]
  change (H.ordinaryPhaseTrajectory t₂ le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) τ.val).1 n = _
  rw [ordinaryPhaseTrajectory,Birkhoff.phaseFlow_fst]
  change Complex.exp _ * _ = Complex.exp _ * _
  rw [← A.finiteGapOrdinaryFrequency_hilbertModel hs H hs₂ E]
  congr 1
  have he := congrArg (fun z : Coeff p × Coeff p => z.1 n)
    (E.complex_map_exponent D h2p (sourceFiniteGapHilbertModel hp hp1 φ hf))
  change _ = (sourceComplexBirkhoffMap hp hp1 t
    (realTypeSourceExponentInclusion h2p (sourceFiniteGapHilbertModel hp hp1 φ hf) : realTypeSourceSubmodule p).val).1 n at he
  rw [sourceFiniteGapHilbertModel_inclusion] at he
  exact he

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
