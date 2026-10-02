import NLS.ZakharovShabat.SourceAngularThetaThetaExponent
import NLS.ZakharovShabat.SourceActionExponentDifferential
import NLS.ZakharovShabat.SourceActionRegularPoisson
import NLS.ZakharovShabat.SourceAngularThetaActionCanonical

/-! # Corollary 13.2 at every finite source exponent above one

All three canonical relations hold for the actual actions and angle
cotangents. Their regular coefficient witnesses give the literal,
absolutely convergent physical Fourier pairing, also below two. Only
an angle's own gap must be open; action gaps may be collapsed.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem thetaActionRegular_bivector_eq_sourceBracket
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (D.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 m) φ.val := by
  change _ = (RegularSourceCotangent.ofCotangent h2p
    (sourceAngularThetaDifferential hp hp1 n s φ.val)).bivector
      (RegularSourceCotangent.ofCotangent h2p (fderiv ℂ (sourceComplexAction hp hp1 m) φ.val))
  exact RegularSourceCotangent.bivector_congr (D.thetaRegularCotangent_toCotangent n φ hn)
    (sourceActionRegularCotangent_toCotangent hp hp1 m φ)

/-- The mixed canonical identity throughout the finite exponent range.
The action index is unrestricted, including at collapsed action gaps. -/
theorem thetaActionRegular_bivector_eq_kronecker
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (D.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
      if n = m then 1 else 0 := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · rw [D.thetaActionRegular_bivector_eq_sourceBracket h2p n m φ hn]
    exact D.thetaAction_eq_kronecker h2p n m φ hn
  · obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
    have hp2 := le_of_not_ge h2p
    let χ := realTypeSourceExponentInclusion hp2 φ
    have hnχ : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n ≠ 0 := by
      dsimp only [χ, realTypeSourceExponentInclusion]
      rw [← canonicalPeriodicGap_source_exponent hp (show (2 : ℝ≥0∞) ≠ ⊤ by simp) hp1 (by norm_num) hp2 φ.val n]
      exact hn
    have heq : (D.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
        (E.thetaRegularCotangent n χ hnχ).bivector (sourceActionRegularCotangent (by simp) (by norm_num) m χ) := by
      unfold RegularSourceCotangent.bivector
      rw [D.thetaRegularCotangent_coefficients_exponent E hp2 n φ hn hnχ,
        sourceActionRegularCotangent_coefficients_exponent hp (show (2 : ℝ≥0∞) ≠ ⊤ by simp)
          hp1 (by norm_num) hp2 m φ]
    rw [heq, E.thetaActionRegular_bivector_eq_sourceBracket (le_refl _) n m χ hnχ]
    exact E.thetaAction_eq_kronecker (le_refl _) n m χ hnχ

/-- All three actual canonical relations on their precise real domains.
Every cotangent used here has proved square-summable Fourier coefficients. -/
theorem corollary13_2_regular
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (sourceActionRegularCotangent hp hp1 n φ).bivector (sourceActionRegularCotangent hp hp1 m φ) = 0 ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      ∀ hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0,
      (D.thetaRegularCotangent n φ hn).bivector (D.thetaRegularCotangent m φ hm) = 0) ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      (D.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
        if n = m then 1 else 0) :=
  ⟨sourceActionRegularCotangent_bivector_eq_zero hp hp1 n m φ,
    D.thetaRegularCotangent_bivector_eq_zero n m φ,
    D.thetaActionRegular_bivector_eq_kronecker n m φ⟩

end SourceAngularThetaCommonDomainData

/-- The proved common-domain construction supplies a single actual
psi family satisfying all canonical relations for every finite `p > 1`. -/
theorem exists_sourceCorollary13_2_regular (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s,
        ∀ n m : ℤ, ∀ φ : realTypeSourceLocus p,
        (sourceActionRegularCotangent hp hp1 n φ).bivector (sourceActionRegularCotangent hp hp1 m φ) = 0 ∧
        (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
          ∀ hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0,
          (D.thetaRegularCotangent n φ hn).bivector (D.thetaRegularCotangent m φ hm) = 0) ∧
        (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
          (D.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
            if n = m then 1 else 0) := by
  obtain ⟨W₀,B,W,_,_,_,_,_,_,s,D⟩ := exists_sourceAngularTheta_theorem13_1_iv hp hp1
  exact ⟨W₀,B,W,s,D,D.corollary13_2_regular⟩

end NLS.ZakharovShabat
