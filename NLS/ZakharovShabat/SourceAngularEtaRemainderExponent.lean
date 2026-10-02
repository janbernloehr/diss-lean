import NLS.ZakharovShabat.SourceAngularBetaExponent
import NLS.ZakharovShabat.SourceAngularEtaCauchyTerminal

/-! # Exponent compatibility of the normalized eta remainder

The omitted root products and both remainder differentials are unchanged
under exponent inclusion. Transport of the normalized sheet primitives
then identifies the actual Cauchy remainder values even when the source
exponents use different annuli, anchors, and Cauchy circles.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

theorem sourceStandardRootOmittedProduct_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (ψ : CoeffPair p) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n ψ z =
      sourceStandardRootOmittedProduct hq hq1 n (CoeffPair.exponentInclusion hpq ψ) z := by
  simp only [sourceStandardRootOmittedProduct, sourceStandardRootOmittedPairedFactor,
    sourceStandardRoot_exponent hp hq hp1 hq1 hpq ψ]

theorem sourceAngularEtaRemainderIntegrand_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) (z : ℂ) :
    sourceAngularEtaRemainderIntegrand hp hp1 n s ψ z =
      sourceAngularEtaRemainderIntegrand hq hq1 n t (CoeffPair.exponentInclusion hpq ψ) z := by
  simp only [sourceAngularEtaRemainderIntegrand, sourceAngularIntegrand,
    sourceAngularEtaModelIntegrand, hnum,
    sourceStandardRoot_exponent hp hq hp1 hq1 hpq ψ,
    sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq ψ]

theorem sourceAngularEtaRemainderSheetIntegrand_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q))) (w z : ℂ) :
    sourceAngularEtaRemainderSheetIntegrand hp hp1 n s ψ w z =
      sourceAngularEtaRemainderSheetIntegrand hq hq1 n t (CoeffPair.exponentInclusion hpq ψ) w z := by
  simp only [sourceAngularEtaRemainderSheetIntegrand, hnum,
    sourceStandardRootOmittedProduct_exponent hp hq hp1 hq1 hpq n ψ,
    sourceAngularRootSheet_exponent hp hq hpq ψ]

theorem sourceAngularEtaRemainderSheetPrimitiveData_exponent_iff
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (n : ℤ) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (t : (k : ℤ) → CoeffPair q → DeletedCoeff q k) (ψ : CoeffPair p)
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q)))
    (c : ℂ) (R : ℝ) (w : ℂ) (F E : ℂ → ℂ) :
    SourceAngularEtaRemainderSheetPrimitiveData hp hp1 n s ψ c R w F E ↔
      SourceAngularEtaRemainderSheetPrimitiveData hq hq1 n t
        (CoeffPair.exponentInclusion hpq ψ) c R w F E := by
  have hseg := sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq ψ n
  have hends := canonicalPeriodicEndpoints_periodOne_exponent hp hq hp1 hq1 hpq ψ
  have hdisc := sourceAngularRegularSheetDisc_exponent hp hq hpq ψ c R w
  have hext := sourceAngularExteriorPrimitive_exponent hp hq hp1 hq1 hpq ψ w F 0
  have hi := sourceAngularEtaRemainderIntegrand_exponent hp hq hp1 hq1 hpq n s t ψ hnum
  have hs := sourceAngularEtaRemainderSheetIntegrand_exponent hp hq hp1 hq1 hpq n s t ψ hnum w
  constructor <;> intro D
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hseg, hends.2] using D.tendsto_right_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩
  · exact ⟨by simpa only [hseg, hi] using D.hasDerivAt_exterior,
      by simpa only [hseg, hends.1] using D.tendsto_left_exterior,
      by simpa only [hseg, hends.2] using D.tendsto_right_exterior,
      by simpa only [hdisc] using D.analytic_sheet,
      by simpa only [hdisc, hs] using D.hasDerivAt_sheet,
      by simpa only [hdisc, hends.1] using D.tendsto_left_sheet,
      by simpa only [hdisc, hends.2] using D.tendsto_right_sheet,
      by simpa only [hdisc, hseg, hext] using D.eqOn_exterior⟩

/-- Different exponents may use entirely different annular charts.
Their actual normalized remainder values still agree, including at endpoints. -/
theorem SourceAngularJointAnnulusChartData.etaRemainderCauchyCandidate_exponent
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {n : ℤ} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    {W V : Set (CoeffPair p)} {W' V' : Set (CoeffPair q)}
    {c c' : ℤ → ℂ} {T T' : ℤ → ℝ} {r R r' R' : ℝ} {z₀ z₀' : ℂ}
    (D : SourceAngularJointAnnulusChartData hp hp1 n s W V c T r R z₀)
    (E : SourceAngularJointAnnulusChartData hq hq1 n t W' V' c' T' r' R' z₀')
    (hpq : p ≤ q) (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ V')
    (hnum : ∀ z, sourcePsiCandidate n (z,(s n ψ : Coeff p)) =
      sourcePsiCandidate n (z,(t n (CoeffPair.exponentInclusion hpq ψ) : Coeff q)))
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (ρ' : ℝ) (hrρ' : r' < ρ') (hρR' : ρ' < R') :
    sourceAngularEtaRemainderCauchyCandidate hp hp1 n s (c n) r R z₀ ρ ψ =
      sourceAngularEtaRemainderCauchyCandidate hq hq1 n t (c' n) r' R' z₀' ρ'
        (CoeffPair.exponentInclusion hpq ψ) := by
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ n
  · rw [D.etaRemainderCauchyCandidate_eq_zero_of_endpoint ψ hψ ρ hend,
      E.etaRemainderCauchyCandidate_eq_zero_of_endpoint _ hψ' ρ'
        ((sourceAngularDirichletTerminalIsEndpoint_exponent_iff hp hq hp1 hq1 hpq ψ n).mp hend)]
  · have hw := sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ n
      (((D.disc_family ψ hψ).contour_family.2 n).2.2.1
        (ball_subset_closedBall ((D.disc_family ψ hψ).dirichlet_mem_ball n)))
      (fun h => hend (Or.inl h)) (fun h => hend (Or.inr h))
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ n hw
    have hC := D.eta_cauchy_sheet_primitive_data ψ hψ ρ hrρ hρR w hw
    have hC' := (sourceAngularEtaRemainderSheetPrimitiveData_exponent_iff
      hp hq hp1 hq1 hpq n s t ψ hnum (c n) r w _ _).mp hC
    have hmu := canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq .dirichlet ψ
    have ha := sourceAntiDiscriminantCandidate_exponent hp hq hp1 hq1 hpq ψ
    have hseg : sourcePeriodicSegment hq hq1 (CoeffPair.exponentInclusion hpq ψ) n ⊆ ball (c n) r := by
      rw [← sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq ψ n]
      exact D.gap_enclosed ψ hψ
    have hb : canonicalPeriodOneBoundaryRoots hq hq1 .dirichlet (CoeffPair.exponentInclusion hpq ψ) n ∈
        sourceAngularRegularSheetDisc hq (CoeffPair.exponentInclusion hpq ψ) (c n) r w := by
      rw [← hmu, ← sourceAngularRegularSheetDisc_exponent hp hq hpq ψ]
      exact ⟨D.terminal_enclosed ψ hψ,hbase.1⟩
    have hroot : sourceAngularRootSheet hq w
        (canonicalPeriodOneBoundaryRoots hq hq1 .dirichlet (CoeffPair.exponentInclusion hpq ψ) n,
          CoeffPair.exponentInclusion hpq ψ) =
        sourceAntiDiscriminantCandidate hq hq1 (CoeffPair.exponentInclusion hpq ψ)
          (canonicalPeriodOneBoundaryRoots hq hq1 .dirichlet (CoeffPair.exponentInclusion hpq ψ) n) := by
      rw [← hmu, ← ha, ← sourceAngularRootSheet_exponent hp hq hpq ψ]
      exact hbase.2
    have heq := E.etaRemainderCauchyCandidate_eq_normalized_terminal _ hψ' ρ' hrρ' hρR'
      hC' hseg hw hb hroot
    dsimp only at heq
    rw [← hmu, hbase.2] at heq
    exact heq.symm

end NLS.ZakharovShabat
