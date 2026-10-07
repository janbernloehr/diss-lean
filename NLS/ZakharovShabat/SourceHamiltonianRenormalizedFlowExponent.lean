import NLS.ZakharovShabat.SourceHamiltonianRenormalizedFlow
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4
import NLS.ZakharovShabat.SourceComplexBirkhoffExponent

/-! # Exponent compatibility of the physical renormalized flow

For `1 < p ≤ q ≤ 2`, including the initial source and then evolving gives
the same result as evolving first. The renormalized frequencies retain
their coefficient-identical values.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {hq : q ≠ ⊤} {hq1 : 1 < q}
variable {W P : Set (CoeffPair p)} {Wq Pq : Set (CoeffPair q)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {sq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- The renormalized frequency is exponent independent. -/
theorem phaseFrequency_exponent
    (A : SourceAbelianMomentAtlas hp hp1 W s) (Q : SourceAbelianMomentAtlas hq hq1 Wq sq)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (hsq : SourcePsiIsolatingComplexExtension hq hq1 Pq sq)
    (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    A.phaseFrequency φ n =
      Q.phaseFrequency (realTypeSourceExponentInclusion hpq φ) n := by
  unfold phaseFrequency
  rw [A.renormalizedFrequency_real_eq_of_coefficients Q hs hsq φ
      (realTypeSourceExponentInclusion hpq φ) (fun _ => ⟨rfl,rfl⟩) n]

/-- The physical Hamiltonian-oriented renormalized flow commutes with inclusion
at all initial sources, for independently constructed compatible exponents. -/
theorem hamiltonianRenormalizedSourceFlow_exponent
    (A : SourceAbelianMomentAtlas hp hp1 W s) (Q : SourceAbelianMomentAtlas hq hq1 Wq sq)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (hsq : SourcePsiIsolatingComplexExtension hq hq1 Pq sq)
    {V B X : Set (CoeffPair p)} {Vq Bq Xq : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {tq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (E : SourceBirkhoffMapComplexData hq hq1 Vq Bq Xq tq)
    (hpq : p ≤ q) (hq2 : q ≤ 2) (φ : realTypeSourceSubmodule p) (time : ℝ) :
    realTypeSourceExponentInclusion hpq (A.hamiltonianRenormalizedSourceFlow D (hpq.trans hq2) φ time) =
      Q.hamiltonianRenormalizedSourceFlow E hq2 (realTypeSourceExponentInclusion hpq φ) time := by
  let L := (Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)
  have hz := D.complex_map_exponent E hpq φ
  have hphase : L (Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) time
      (sourceComplexBirkhoffMap hp hp1 t φ.val)) =
      Birkhoff.hamiltonianPhaseFlow (Q.phaseFrequency (realTypeSourceExponentInclusion hpq φ)) time
        (sourceComplexBirkhoffMap hq hq1 tq (realTypeSourceExponentInclusion hpq φ).val) := by
    apply Prod.ext
    · ext n
      change Complex.exp _ * _ = Complex.exp _ * _
      dsimp only
      rw [← A.phaseFrequency_exponent Q hs hsq hpq φ n]
      congr 1
      exact congrArg (fun z : Coeff q × Coeff q => z.1 n) hz
    · ext n
      change (Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency φ) time
        (sourceComplexBirkhoffMap hp hp1 t φ.val)).2 n = _
      simp only [Birkhoff.hamiltonianPhaseFlow_snd]
      rw [← A.phaseFrequency_exponent Q hs hsq hpq φ n]
      congr 1
      exact congrArg (fun z : Coeff q × Coeff q => z.2 n) hz
  apply E.complex_map_real_injective
  exact (D.complex_map_exponent E hpq _).symm.trans
    ((congrArg L (A.complex_map_hamiltonianRenormalizedSourceFlow D (hpq.trans hq2) φ time)).trans
      (hphase.trans (Q.complex_map_hamiltonianRenormalizedSourceFlow E hq2
        (realTypeSourceExponentInclusion hpq φ) time).symm))

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
