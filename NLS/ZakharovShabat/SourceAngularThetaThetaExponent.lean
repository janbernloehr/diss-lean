import NLS.ZakharovShabat.SourceAngularThetaRegularCotangent
import NLS.ZakharovShabat.SourceAngularThetaThetaHilbert
import NLS.SequenceSpaces.FiniteSourceCoefficients

/-! # Angle commutation at every finite source exponent

Hilbert angle commutation transfers first to finite Fourier sources
at larger exponents. Norm-convergent real Fourier truncations then give
all real sources above two. Below two, the actual regular cotangents
restrict from Hilbert space, preserving their full coefficient pairing.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Every finite Fourier real source is the inclusion of an actual
real Hilbert source. This concerns Fourier support, not finite gaps. -/
theorem exists_realHilbertSource_of_finite_support (h2p : (2 : ℝ≥0∞) ≤ p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hleft : Coeff.HasFiniteSupport ψ.fst) (hright : Coeff.HasFiniteSupport ψ.snd) :
    ∃ φ : realTypeSourceLocus 2, CoeffPair.exponentInclusion h2p φ.val = ψ := by
  classical
  obtain ⟨S,hS⟩ := hleft
  obtain ⟨T,hT⟩ := hright
  let a : ℤ →₀ ℂ := Finsupp.onFinset S ψ.fst (fun n hn => by by_contra h; exact hn (hS n h))
  let b : ℤ →₀ ℂ := Finsupp.onFinset T ψ.snd (fun n hn => by by_contra h; exact hn (hT n h))
  let φ : CoeffPair 2 := CoeffPair.ofFinsupp (a,b)
  have hφ : IsRealType (CoeffPair.toMax 2 φ) := by
    intro n
    exact hreal n
  refine ⟨⟨φ,hφ⟩,?_⟩
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n <;> rfl

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem thetaThetaBracket_exponent
    {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (h2p : (2 : ℝ≥0∞) ≤ p) (hpq : p ≤ q) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val =
      sourceAngularThetaThetaBracket hq hq1 (h2p.trans hpq) n m t
        (CoeffPair.exponentInclusion hpq φ.val) := by
  unfold sourceAngularThetaThetaBracket
  rw [D.thetaDifferential_exponent E hpq n φ hn, D.thetaDifferential_exponent E hpq m φ hm]
  exact sourceBivector_restrict_exponent h2p hpq _ _

/-- Full angle/angle involution above two, obtained from the Hilbert
identity by finite Fourier approximation in the actual source norm. -/
theorem thetaThetaBracket_eq_zero_of_two_le
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val = 0 := by
  obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
  apply D.thetaThetaBracket_eq_zero_of_finite_realType h2p n m ?_ φ.val (D.real_subset φ.property) φ.property hn hm
  intro ψ _ hreal hleft hright hnψ hmψ
  obtain ⟨χ,hχ⟩ := exists_realHilbertSource_of_finite_support h2p ψ hreal hleft hright
  have hnχ : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n ≠ 0 := by
    rw [canonicalPeriodicGap_source_exponent (by simp) hp (by norm_num) hp1 h2p χ.val n, hχ]
    exact hnψ
  have hmχ : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential χ.val) (periodOnePotential_mem χ.val) m ≠ 0 := by
    rw [canonicalPeriodicGap_source_exponent (by simp) hp (by norm_num) hp1 h2p χ.val m, hχ]
    exact hmψ
  have heq := E.thetaThetaBracket_exponent D (le_refl _) h2p n m χ hnχ hmχ
  rw [hχ] at heq
  exact heq.symm.trans (E.thetaThetaBracket_eq_zero_of_realType n m χ hnχ hmχ)

/-- The actual regular angle cotangents commute for every finite
exponent above one, with only their own two gaps required to be open. -/
theorem thetaRegularCotangent_bivector_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (D.thetaRegularCotangent n φ hn).bivector (D.thetaRegularCotangent m φ hm) = 0 := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · rw [D.thetaRegularCotangent_bivector_eq_sourceBivector h2p n m φ hn hm]
    exact D.thetaThetaBracket_eq_zero_of_two_le h2p n m φ hn hm
  · obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
    have hp2 := le_of_not_ge h2p
    let χ := realTypeSourceExponentInclusion hp2 φ
    have hnχ : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential χ.val) (periodOnePotential_mem χ.val) n ≠ 0 := by
      dsimp only [χ, realTypeSourceExponentInclusion]
      rw [← canonicalPeriodicGap_source_exponent hp (show (2 : ℝ≥0∞) ≠ ⊤ by simp) hp1 (by norm_num) hp2 φ.val n]
      exact hn
    have hmχ : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential χ.val) (periodOnePotential_mem χ.val) m ≠ 0 := by
      dsimp only [χ, realTypeSourceExponentInclusion]
      rw [← canonicalPeriodicGap_source_exponent hp (show (2 : ℝ≥0∞) ≠ ⊤ by simp) hp1 (by norm_num) hp2 φ.val m]
      exact hm
    have heq : (D.thetaRegularCotangent n φ hn).bivector (D.thetaRegularCotangent m φ hm) =
        (E.thetaRegularCotangent n χ hnχ).bivector (E.thetaRegularCotangent m χ hmχ) := by
      unfold RegularSourceCotangent.bivector
      rw [D.thetaRegularCotangent_coefficients_exponent E hp2 n φ hn hnχ,
        D.thetaRegularCotangent_coefficients_exponent E hp2 m φ hm hmχ]
    rw [heq, E.thetaRegularCotangent_bivector_eq_sourceBivector (le_refl _) n m χ hnχ hmχ]
    exact E.thetaThetaBracket_eq_zero_of_realType n m χ hnχ hmχ

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
