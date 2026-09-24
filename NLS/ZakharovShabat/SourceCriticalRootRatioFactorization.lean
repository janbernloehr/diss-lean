import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsed

/-!
# Separating the selected gap factor in the critical-root ratio

Off every periodic gap, the discriminant derivative divided by the
canonical root is the one selected critical factor over its standard
root, times the deleted quotient of Corollary 10.6. The deleted
quotient remains analytic across the selected gap and is the regular
factor needed for the open-gap contour argument in Lemma 10.11(ii).
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Factorization of the actual critical-root integrand on the full
gap complement, for every source potential and every index. -/
theorem sourceCriticalRootRatio_eq_selectedFactor_mul_extension
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z =
      ((canonicalCriticalPoints hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n-z) /
        sourceStandardRoot hp hp1 ψ n z) *
          sourceCriticalRootRatioExtension hp hp1 n ψ z := by
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hseq : displacedRoots a = canonicalCriticalPoints hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) := by
    funext m
    simp only [a, displacedRoots, canonicalCriticalDisplacement_apply]
    ring
  have hderiv := discriminant_derivative_eq_canonicalCriticalProduct hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z
  rw [← hseq] at hderiv
  have hfactor := jointSingleSpectralProduct_eq_deleted hp hp1 n (z,a)
  have hroot := sourceCanonicalRoot_eq_omitted hp hp1 n ψ z
  have hstd : sourceStandardRoot hp hp1 ψ n z ≠ 0 :=
    sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n)
  have homit : sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n
      (fun m _ => hz m)
  rw [hderiv]
  rw [← hseq]
  change jointSingleSpectralProduct (z,a) / sourceCanonicalRoot hp hp1 ψ z =
    ((displacedRoots a n-z) / sourceStandardRoot hp hp1 ψ n z) *
      (-I * (jointDeletedSingleSpectralProduct n (z,a) /
        sourceStandardRootOmittedProduct hp hp1 n ψ z))
  rw [hfactor,hroot]
  field_simp [hstd,homit]
  simp

/-- The deleted factor is analytic through the selected gap on a
single almost-real source domain, whether the gap is open or closed. -/
theorem exists_global_sourceCriticalRootRatioExtension_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
          (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  obtain ⟨W,hWopen,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n z hz
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hQ : AnalyticAt ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      (z,(a,ψ)) := (hdata n).2 (z,(a,ψ)) ⟨hψ,hz⟩
  have hmap : AnalyticAt ℂ (fun w : ℂ => (w,(a,ψ))) z :=
    analyticAt_id.prod (analyticAt_const.prod analyticAt_const)
  change AnalyticAt ℂ (fun w =>
    -I * sourceSingleRootQuotientJointProduct hp hp1 n (w,(a,ψ))) z
  exact analyticAt_const.mul
    (hQ.comp (f := fun w : ℂ => (w,(a,ψ))) hmap)

end NLS.ZakharovShabat
