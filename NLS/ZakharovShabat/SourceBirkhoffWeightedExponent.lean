import NLS.SequenceSpaces.WeightedRealExponent
import NLS.ZakharovShabat.SourceWeightedRealExponent
import NLS.ZakharovShabat.SourceBirkhoffOriginalWeightedMap
import NLS.ZakharovShabat.SourceSection14

/-! # Weighted real Birkhoff maps agree across exponents

The original map commutes with coefficient-preserving inclusions for every
Section 6 spectral weight and every finite 1<p<=q. The two maps may come from
independent normalized families. This proves weighted real compatibility;
the weighted complex analytic extension remains separate work.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
  {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}

/-- Independently constructed original weighted real maps commute with exponent inclusion. -/
theorem originalWeightedRealMap_exponent
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C V t)
    (w : SpectralWeight) (hpq : p ≤ q) (a : weightedRealSourceSubmodule (p := p) w) :
    WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq
      (D.originalWeightedRealMap w a) =
        E.originalWeightedRealMap w (weightedRealSourceExponentInclusion w hpq a) := by
  have h := D.real_map_exponent E hpq (originalWeightedRealSource w a)
  apply (WithLp.equiv q _).injective
  apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext <;> funext n
  · change (WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq
        (D.originalWeightedRealMap w a)).fst.val.val n =
          (E.originalWeightedRealMap w (weightedRealSourceExponentInclusion w hpq a)).fst.val.val n
    simp only [WeightedRealCoeff.pairExponentInclusion_fst,
      WeightedRealCoeff.exponentInclusion_apply, originalWeightedRealMap_fst,
      originalWeightedRealSource_exponent]
    exact congrArg Complex.ofReal (congrArg (fun z : RealCoeff q × RealCoeff q => z.1 n) h)
  · change (WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq
        (D.originalWeightedRealMap w a)).snd.val.val n =
          (E.originalWeightedRealMap w (weightedRealSourceExponentInclusion w hpq a)).snd.val.val n
    simp only [WeightedRealCoeff.pairExponentInclusion_snd,
      WeightedRealCoeff.exponentInclusion_apply, originalWeightedRealMap_snd,
      originalWeightedRealSource_exponent]
    exact congrArg Complex.ofReal (congrArg (fun z : RealCoeff q × RealCoeff q => z.2 n) h)
end SourceBirkhoffMapComplexData

/-- Any two actual Section 14 constructions give the same weighted real map after inclusion. -/
theorem SourceSection14Data.weighted_real_exponent
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {hq : q ≠ ⊤} {hq1 : 1 < q} {A B C : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceSection14Data hp hp1 W₀ W V s) (E : SourceSection14Data hq hq1 A B C t)
    (w : SpectralWeight) (hpq : p ≤ q) (a : weightedRealSourceSubmodule (p := p) w) :
    WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq
      (D.complex.originalWeightedRealMap w a) =
        E.complex.originalWeightedRealMap w (weightedRealSourceExponentInclusion w hpq a) :=
  D.complex.originalWeightedRealMap_exponent E.complex w hpq a

/-- Construct compatible original weighted real maps for every pair of finite exponents above one. -/
theorem sourceSection14_weighted_real_compatible
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q) (hpq : p ≤ q) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s,
        ∃ A B C : Set (CoeffPair q), ∃ t : (n : ℤ) → CoeffPair q → DeletedCoeff q n,
          ∃ E : SourceSection14Data hq hq1 A B C t,
            ∀ w : SpectralWeight, ∀ a : weightedRealSourceSubmodule (p := p) w,
              WeightedRealCoeff.pairExponentInclusion (sourceFrequencyWeight w) hpq
                (D.complex.originalWeightedRealMap w a) =
                  E.complex.originalWeightedRealMap w (weightedRealSourceExponentInclusion w hpq a) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 hp hp1
  obtain ⟨A,B,C,t,E⟩ := sourceSection14 hq hq1
  exact ⟨W₀,W,V,s,D,A,B,C,t,E,fun w a => D.weighted_real_exponent E w hpq a⟩

end NLS.ZakharovShabat
