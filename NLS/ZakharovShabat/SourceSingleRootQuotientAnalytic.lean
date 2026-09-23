import NLS.ZakharovShabat.JointDeletedSingleSpectralProducts
import NLS.ZakharovShabat.SourceStandardRootOmittedJointAnalytic

/-!
# Corollary 10.6: analytic single-root quotient

The numerator deletes the same integer index as the standard-root
denominator. The former is jointly entire; the latter is jointly analytic
and nonzero on the open moving-gap complement of Lemma 10.5. Their quotient
is therefore analytic in the spectral parameter, the `ℓᵖ` displacement
sequence, and the source potential.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The product of Corollary 10.6 as the quotient of the deleted numerator
and the standard-root product with the same index omitted. -/
def sourceSingleRootQuotientJointProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) : ℂ × (Coeff p × CoeffPair p) → ℂ :=
  fun t => jointDeletedSingleSpectralProduct n (t.1,t.2.1) /
    sourceStandardRootOmittedJointProduct hp hp1 n (t.1,t.2.2)

/-- The open joint domain, excluding all standard-root gaps except the
gap whose index was deleted. -/
def sourceSingleRootQuotientJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) :
    Set (ℂ × (Coeff p × CoeffPair p)) :=
  {t | (t.1,t.2.2) ∈ sourceStandardRootOmittedJointDomain hp hp1 W n}

/-- The literal finite product of single-root over standard-root factors
with one common index omitted. -/
def sourceSingleRootQuotientPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (N : ℕ) : ℂ × (Coeff p × CoeffPair p) → ℂ :=
  fun t => ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
    (displacedRoots t.2.1 m-t.1) / sourceStandardRoot hp hp1 t.2.2 m t.1

/-- The finite quotient of the separately normalized products is exactly
the literal finite product wherever its standard roots are nonzero. -/
theorem sourceSingleRootQuotientPartialProduct_eq_div
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (W : Set (CoeffPair p)) (t : ℂ × (Coeff p × CoeffPair p))
    (ht : t ∈ sourceSingleRootQuotientJointDomain hp hp1 W n) :
    sourceSingleRootQuotientPartialProduct hp hp1 n N t =
      jointDeletedSingleSpectralPartialProduct n N (t.1,t.2.1) /
        sourceStandardRootOmittedPartialProduct hp hp1 n N (t.1,t.2.2) := by
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n
  let A : ℂ := ∏ m ∈ s, (displacedRoots t.2.1 m-t.1)
  let B : ℂ := ∏ m ∈ s, sourceStandardRoot hp hp1 t.2.2 m t.1
  let D : ℂ := ∏ m ∈ s, singleSpectralDenominator m
  have hgap : t.1 ∈ sourceStandardRootOmittedDomain hp hp1 t.2.2 n := ht.2
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact sourceStandardRoot_ne_zero_off_segment hp hp1 t.2.2 m t.1
      (hgap m (Finset.mem_erase.mp hm).1)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact Finset.prod_ne_zero_iff.mpr (fun m _ => singleSpectralDenominator_ne_zero m)
  change (∏ m ∈ s, (displacedRoots t.2.1 m-t.1) /
      sourceStandardRoot hp hp1 t.2.2 m t.1) =
    ((∏ m ∈ s, (displacedRoots t.2.1 m-t.1) /
      singleSpectralDenominator m) / singleSpectralDenominator n) /
    ((∏ m ∈ s, sourceStandardRoot hp hp1 t.2.2 m t.1 /
      singleSpectralDenominator m) / singleSpectralDenominator n)
  simp only [Finset.prod_div_distrib]
  dsimp only [A, B, D] at hB hD ⊢
  field_simp [hB, hD, singleSpectralDenominator_ne_zero n]

/-- The literal products in Corollary 10.6 converge to the analytic
quotient at every point of the moving-gap complement. -/
theorem tendsto_sourceSingleRootQuotientPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (W : Set (CoeffPair p)) (t : ℂ × (Coeff p × CoeffPair p))
    (ht : t ∈ sourceSingleRootQuotientJointDomain hp hp1 W n) :
    Tendsto (fun N => sourceSingleRootQuotientPartialProduct hp hp1 n N t)
      atTop (𝓝 (sourceSingleRootQuotientJointProduct hp hp1 n t)) := by
  have hnum := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n (t.1,t.2.1)
  have hden := tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n t.2.2 t.1
  have hden0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 t.2.2 t.1 n ht.2
  have hdiv := hnum.div hden hden0
  change Tendsto (fun N =>
      jointDeletedSingleSpectralPartialProduct n N (t.1,t.2.1) /
        sourceStandardRootOmittedPartialProduct hp hp1 n N (t.1,t.2.2))
    atTop (𝓝 (sourceSingleRootQuotientJointProduct hp hp1 n t)) at hdiv
  exact hdiv.congr' (Filter.Eventually.of_forall (fun N =>
    (sourceSingleRootQuotientPartialProduct_eq_div hp hp1 n N W t ht).symm))

/-- The quotient domain is open whenever the corresponding standard-root
joint domain is open. -/
theorem isOpen_sourceSingleRootQuotientJointDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) (n : ℤ)
    (hD : IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n)) :
    IsOpen (sourceSingleRootQuotientJointDomain hp hp1 W n) := by
  change IsOpen ((fun t : ℂ × (Coeff p × CoeffPair p) => (t.1,t.2.2)) ⁻¹'
    sourceStandardRootOmittedJointDomain hp hp1 W n)
  exact hD.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

/-- The joint quotient is analytic wherever all remaining standard roots
avoid their gap segments. -/
theorem sourceSingleRootQuotientJointProduct_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (W : Set (CoeffPair p))
    (hroot : AnalyticOnNhd ℂ (sourceStandardRootOmittedJointProduct hp hp1 n)
      (sourceStandardRootOmittedJointDomain hp hp1 W n))
    (hroot0 : ∀ q ∈ sourceStandardRootOmittedJointDomain hp hp1 W n,
      sourceStandardRootOmittedJointProduct hp hp1 n q ≠ 0) :
    AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
      (sourceSingleRootQuotientJointDomain hp hp1 W n) := by
  intro t ht
  have hnumProj : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.1)) t :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hrootProj : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) t :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hnum : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) =>
        jointDeletedSingleSpectralProduct n (q.1,q.2.1)) t :=
    ((analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 n)
      (t.1,t.2.1) (mem_univ _)).comp
        (f := fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.1)) hnumProj
  have hden : AnalyticAt ℂ
      (fun q : ℂ × (Coeff p × CoeffPair p) =>
        sourceStandardRootOmittedJointProduct hp hp1 n (q.1,q.2.2)) t :=
    (hroot (t.1,t.2.2) ht).comp
      (f := fun q : ℂ × (Coeff p × CoeffPair p) => (q.1,q.2.2)) hrootProj
  exact hnum.div hden (hroot0 (t.1,t.2.2) ht)

/-- One connected almost-real source domain supports the quotient in
Corollary 10.6 for every deleted integer index. -/
theorem exists_global_source_analytic_singleRootQuotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ,
        IsOpen (sourceSingleRootQuotientJointDomain hp hp1 W n) ∧
        AnalyticOnNhd ℂ (sourceSingleRootQuotientJointProduct hp hp1 n)
          (sourceSingleRootQuotientJointDomain hp hp1 W n) := by
  obtain ⟨W,hWopen,hWconn,hreal,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  refine ⟨W,hWopen,hWconn,hreal,?_⟩
  intro n
  obtain ⟨hD,hroot,_,hroot0⟩ := hdata n
  exact ⟨isOpen_sourceSingleRootQuotientJointDomain hp hp1 W n hD,
    sourceSingleRootQuotientJointProduct_analyticOnNhd hp hp1 n W hroot hroot0⟩

end NLS.ZakharovShabat
