import NLS.ZakharovShabat.SourceAngularThetaThetaHilbert
import NLS.ZakharovShabat.SourceAngularThetaActionCanonical
import NLS.ZakharovShabat.SourceDiscriminantPoisson

/-!
# Corollary 13.2 at the Hilbert exponent

The actual indexed actions commute at every real Hilbert source. The
actual angles commute where their two selected gaps are open, and the
angle/action bracket is the Kronecker delta where its angle gap is open.
All three identities use the same constructed normalized psi family
and actual angle differentials, with the physical Poisson sign.

Extension to other exponents remains separate from this Hilbert result.
-/

noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- All three canonical identities hold on their respective real
Hilbert source domains. Only an angle's own gap is required to be open. -/
theorem SourceAngularThetaCommonDomainData.corollary13_2_hilbert
    {W₀ B W : Set (CoeffPair 2)} {s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j}
    (D : SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus 2) :
    sourceBracket (by norm_num) (sourceComplexAction (by simp) (by norm_num) n)
      (sourceComplexAction (by simp) (by norm_num) m) φ.val = 0 ∧
    (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
      sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val = 0) ∧
    (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
      sourceAngularThetaFunctionalBracket (by simp) (by norm_num) (by norm_num) n s
        (sourceComplexAction (by simp) (by norm_num) m) φ.val = if n = m then 1 else 0) :=
  ⟨sourceBracket_actions_eq_zero (by simp) (by norm_num) (by norm_num) φ.val φ.property n m,
    D.thetaThetaBracket_eq_zero_of_realType n m φ,
    D.thetaAction_eq_kronecker (by norm_num) n m φ⟩

/-- The constructed common analytic source domain and normalized
family satisfy all Hilbert canonical relations. No supplied finite-gap
or endpoint condition is needed. -/
theorem exists_sourceCorollary13_2_hilbert :
    ∃ W₀ B W : Set (CoeffPair 2),
      ∃ s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j,
        SourceAngularThetaCommonDomainData (p := 2) (by simp) (by norm_num) W₀ B W s ∧
        ∀ n m : ℤ, ∀ φ : realTypeSourceLocus 2,
          sourceBracket (by norm_num) (sourceComplexAction (by simp) (by norm_num) n)
            (sourceComplexAction (by simp) (by norm_num) m) φ.val = 0 ∧
          (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
            canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 →
            sourceAngularThetaThetaBracket (by simp) (by norm_num) (by norm_num) n m s φ.val = 0) ∧
          (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
            sourceAngularThetaFunctionalBracket (by simp) (by norm_num) (by norm_num) n s
              (sourceComplexAction (by simp) (by norm_num) m) φ.val = if n = m then 1 else 0) := by
  obtain ⟨W₀,B,W,_,_,_,_,_,_,s,D⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,D.corollary13_2_hilbert⟩

end NLS.ZakharovShabat
