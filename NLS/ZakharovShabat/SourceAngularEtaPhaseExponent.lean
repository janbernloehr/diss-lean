import NLS.ZakharovShabat.SourceAngularEtaRemainderExponent
import NLS.ZakharovShabat.SourceAngularThetaTheorem13_1

/-! # Exponent compatibility of the actual eta phase

The terminal sine and cosine coordinates agree up to the half-gap sign.
Together with the normalized remainder comparison this identifies eta
modulo pi across arbitrary charts and source exponents. The constructed
common-domain families supply numerator agreement at every real source.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem canonicalPeriodicMidpoint_source_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (ψ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicMidpoint hq hq1 (periodOnePotential (CoeffPair.exponentInclusion hpq ψ))
        (periodOnePotential_mem _) n := by
  unfold canonicalPeriodicMidpoint
  rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).2]

theorem canonicalPeriodicGap_source_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (ψ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicGap hq hq1 (periodOnePotential (CoeffPair.exponentInclusion hpq ψ))
        (periodOnePotential_mem _) n := by
  unfold canonicalPeriodicGap
  rw [(canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).1,
    (canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ).2]

/-- Terminal angles on arbitrary half-gap branches agree modulo pi
across exponents, also when the Dirichlet terminal is periodic. -/
theorem SourceAngularComplexDirichletAngleData.angle_sub_eq_int_pi_exponent
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q} {m : ℤ}
    {W U : Set (CoeffPair p)} {W' U' : Set (CoeffPair q)}
    {δ ε : CoeffPair p → ℂ} {δ' ε' : CoeffPair q → ℂ}
    (D : SourceAngularComplexDirichletAngleData hp hp1 m W U δ ε)
    (E : SourceAngularComplexDirichletAngleData hq hq1 m W' U' δ' ε')
    (hpq : p ≤ q) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ U') :
    ∃ k : ℤ, ε ψ - ε' (CoeffPair.exponentInclusion hpq ψ) = (k : ℂ) * (Real.pi : ℂ) := by
  let χ := CoeffPair.exponentInclusion hpq ψ
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  have hmu := canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet ψ
  have hτ := canonicalPeriodicMidpoint_source_exponent hp hq hp1 hq1 hpq ψ m
  have hcos : Complex.cos (ε ψ) = (μ-τ)/δ ψ := by
    apply (eq_div_iff (D.halfGap_ne_zero ψ hψ)).mpr
    have hpoint := (D.terminal_coordinates ψ hψ).1
    change τ + δ ψ * Complex.cos (ε ψ) = μ at hpoint
    linear_combination hpoint
  have hcos' : Complex.cos (ε' χ) = (μ-τ)/δ' χ := by
    apply (eq_div_iff (E.halfGap_ne_zero χ hψ')).mpr
    have hpoint := (E.terminal_coordinates χ hψ').1
    change canonicalPeriodicMidpoint hq hq1 (periodOnePotential χ) (periodOnePotential_mem χ) m +
      δ' χ * Complex.cos (ε' χ) = canonicalPeriodOneBoundaryRoots hq hq1 .dirichlet χ m at hpoint
    rw [← hτ, ← hmu] at hpoint
    change τ + δ' χ * Complex.cos (ε' χ) = μ at hpoint
    linear_combination hpoint
  have hsine := (D.terminal_coordinates ψ hψ).2
  have hsine' := (E.terminal_coordinates χ hψ').2
  simp only [sourceAngularBranchDirichletSine] at hsine hsine'
  dsimp only [χ] at hsine'
  rw [← hmu, ← sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq ψ,
    ← sourceStandardRootOmittedProduct_exponent hp hq hp1 hq1 hpq m ψ] at hsine'
  have hsq : δ ψ ^ 2 = δ' χ ^ 2 := by
    rw [D.halfGap_sq ψ hψ, E.halfGap_sq χ hψ', canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq ψ m]
  rcases eq_or_eq_neg_of_sq_eq_sq (δ ψ) (δ' χ) hsq with hd | hd
  · apply angle_sub_eq_int_pi_of_coordinates_up_to_sign (ε ψ) (ε' χ) 1 (Or.inl rfl)
    · rw [hsine, hsine', hd, one_mul]
    · rw [hcos, hcos', hd, one_mul]
  · apply angle_sub_eq_int_pi_of_coordinates_up_to_sign (ε ψ) (ε' χ) (-1) (Or.inr rfl)
    · rw [hsine, hsine', hd]
      simp only [mul_neg, neg_mul, div_neg, one_mul, χ]
    · rw [hcos, hcos', hd, div_neg, neg_one_mul]

/-- Actual eta representatives differ by an integer multiple of pi,
with no matching of annuli or angle branches required. -/
theorem SourceAngularEtaAnalyticChartData.representative_sub_eq_int_pi_exponent
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {n : ℤ} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    {W V U : Set (CoeffPair p)} {W' V' U' : Set (CoeffPair q)}
    {c c' : ℤ → ℂ} {T T' : ℤ → ℝ} {r R r' R' : ℝ} {z₀ z₀' : ℂ} {ρ ρ' : ℝ}
    {δ ε : CoeffPair p → ℂ} {δ' ε' : CoeffPair q → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (E : SourceAngularEtaAnalyticChartData hq hq1 n t W' V' U' c' T' r' R' z₀' ρ' δ' ε')
    (hpq : p ≤ q) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ U')
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    ∃ k : ℤ, sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ -
      sourceAngularEtaCauchyRepresentative hq hq1 n t (c' n) r' R' z₀' ρ' ε'
        (CoeffPair.exponentInclusion hpq ψ) = (k : ℂ) * (Real.pi : ℂ) := by
  obtain ⟨k,hk⟩ := D.angle.angle_sub_eq_int_pi_exponent E.angle hpq ψ hψ hψ'
  have hR := D.annulus.etaRemainderCauchyCandidate_exponent E.annulus hpq ψ
    (D.angle.source_subset hψ) (E.angle.source_subset hψ') hnum
    ρ D.inner_lt_cauchy D.cauchy_lt_outer ρ' E.inner_lt_cauchy E.cauchy_lt_outer
  refine ⟨k,?_⟩
  simp only [sourceAngularEtaCauchyRepresentative]
  rw [hR]
  linear_combination hk

theorem SourceAngularEtaAnalyticChartData.phase_exponent
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {n : ℤ} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    {W V U : Set (CoeffPair p)} {W' V' U' : Set (CoeffPair q)}
    {c c' : ℤ → ℂ} {T T' : ℤ → ℝ} {r R r' R' : ℝ} {z₀ z₀' : ℂ} {ρ ρ' : ℝ}
    {δ ε : CoeffPair p → ℂ} {δ' ε' : CoeffPair q → ℂ}
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (E : SourceAngularEtaAnalyticChartData hq hq1 n t W' V' U' c' T' r' R' z₀' ρ' δ' ε')
    (hpq : p ≤ q) (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ U')
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) :
    sourceAngularEtaAnalyticPhase hp hp1 n s ψ =
      sourceAngularEtaAnalyticPhase hq hq1 n t (CoeffPair.exponentInclusion hpq ψ) := by
  rw [D.phase_eq_exp_representative ψ hψ, E.phase_eq_exp_representative _ hψ']
  obtain ⟨k,hk⟩ := D.representative_sub_eq_int_pi_exponent E hpq ψ hψ hψ' hnum
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  exact ⟨k,by linear_combination 2*I*hk⟩

/-- The actual common-domain eta phases agree at every real open gap.
Both the charts and numerator compatibility are provided by proved constructions. -/
theorem SourceAngularThetaCommonDomainData.etaPhase_real_exponent_agreement
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W₀ B W : Set (CoeffPair p)} {V₀ C V : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularEtaAnalyticPhase hp hp1 n s φ.val =
      sourceAngularEtaAnalyticPhase hq hq1 n t (CoeffPair.exponentInclusion hpq φ.val) := by
  have hgap' : canonicalPeriodicGap hq hq1
      (periodOnePotential (CoeffPair.exponentInclusion hpq φ.val)) (periodOnePotential_mem _) n ≠ 0 := by
    rw [← canonicalPeriodicGap_source_exponent hp hq hp1 hq1 hpq φ.val n]
    exact hgap
  obtain ⟨A,U,c,T,r,R,z₀,ρ,δ,ε,hφ,_,_,H⟩ := D.local_charts n φ.val (D.real_subset φ.property) hgap
  obtain ⟨A',U',c',T',r',R',z₀',ρ',δ',ε',hφ',_,_,H'⟩ := E.local_charts n _
    (E.real_subset (realTypeSourceExponentInclusion hpq φ).property) hgap'
  exact H.phase_exponent H' hpq φ.val hφ hφ'
    (D.psi.toSourcePsiIsolatingComplexExtension.candidate_real_exponent_agreement
      E.psi.toSourcePsiIsolatingComplexExtension hpq n φ)

end NLS.ZakharovShabat
