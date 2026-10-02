import NLS.ZakharovShabat.SourceAngularThetaExponent
import NLS.Poisson.RegularSourceCotangent

/-! # Square-summable coefficients of the actual angle differential

Above two, continuity gives Hilbert coefficients. Below two, the actual
angle differential is the restriction of a constructed Hilbert angle
differential. Coefficient uniqueness makes the result independent of
that auxiliary construction and preserves it under exponent inclusion.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_regular_thetaDifferential
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    ∃ L : RegularSourceCotangent p, L.toCotangent = sourceAngularThetaDifferential hp hp1 n s φ.val := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · exact ⟨RegularSourceCotangent.ofCotangent h2p _,rfl⟩
  · obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
    let L := RegularSourceCotangent.ofCotangent (le_refl (2 : ℝ≥0∞))
      (sourceAngularThetaDifferential (by simp) (by norm_num) n t
        (CoeffPair.exponentInclusion (le_of_not_ge h2p) φ.val))
    exact ⟨L.restrict (le_of_not_ge h2p),
      (D.thetaDifferential_exponent E (le_of_not_ge h2p) n φ hn).symm⟩

/-- A regular cotangent for the actual angle, only on its open-gap domain. -/
def thetaRegularCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    RegularSourceCotangent p := (D.exists_regular_thetaDifferential n φ hn).choose

@[simp] theorem thetaRegularCotangent_toCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (D.thetaRegularCotangent n φ hn).toCotangent = sourceAngularThetaDifferential hp hp1 n s φ.val :=
  (D.exists_regular_thetaDifferential n φ hn).choose_spec

/-- The complete Hilbert coefficient pair is preserved, not just one bracket. -/
theorem thetaRegularCotangent_coefficients_exponent
    {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hn' : canonicalPeriodicGap hq hq1 (periodOnePotential (CoeffPair.exponentInclusion hpq φ.val))
      (periodOnePotential_mem _) n ≠ 0) :
    (D.thetaRegularCotangent n φ hn).coefficients =
      (E.thetaRegularCotangent n (realTypeSourceExponentInclusion hpq φ) hn').coefficients := by
  apply RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
    (D.thetaRegularCotangent n φ hn)
    ((E.thetaRegularCotangent n (realTypeSourceExponentInclusion hpq φ) hn').restrict hpq)
  exact (D.thetaRegularCotangent_toCotangent n φ hn).trans
    ((D.thetaDifferential_exponent E hpq n φ hn).trans
      (congrArg (fun L : CoeffPair q →L[ℂ] ℂ => L.comp (CoeffPair.exponentInclusion hpq))
        (E.thetaRegularCotangent_toCotangent n (realTypeSourceExponentInclusion hpq φ) hn')).symm)

/-- On the old exponent range the regular pairing is exactly the
existing source bivector of the full angle differentials. -/
theorem thetaRegularCotangent_bivector_eq_sourceBivector
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (D.thetaRegularCotangent n φ hn).bivector (D.thetaRegularCotangent m φ hm) =
      sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
        (sourceAngularThetaDifferential hp hp1 m s φ.val) := by
  rw [← RegularSourceCotangent.bivector_ofCotangent h2p]
  exact RegularSourceCotangent.bivector_congr
    (D.thetaRegularCotangent_toCotangent n φ hn) (D.thetaRegularCotangent_toCotangent m φ hm)

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
