import NLS.Articles.KdVPseudomeasures.SpectralComplexGaps
import NLS.Articles.KdVPseudomeasures.SpectralEndpointBootstrap
import NLS.SequenceSpaces.OrderedNatEnumerationUnique

/-! Intrinsic original spectral data are independent of the endpoint predual
order used to realize the same entire physical distribution. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- The original H-minus-one potential does not depend on its endpoint realization. -/
theorem sourceComplexHminusOne_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) : sourceComplexHminusOne r hr q = sourceComplexHminusOne t ht v := by
  apply Subtype.ext
  rw [sourceComplexHminusOne_val, sourceComplexHminusOne_val]
  exact h

/-- Equality is of the full original operator on its unchanged H1 domain. -/
theorem sourceHillOperator_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) :
    singularHillOperator (sourceComplexHminusOne r hr q) =
      singularHillOperator (sourceComplexHminusOne t ht v) := by
  rw [sourceComplexHminusOne_eq_of_distribution_eq r t hr ht q v h]

/-- The entire complex spectrum is intrinsic to the original distribution. -/
theorem sourceHillSpectrum_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) : sourceHillSpectrum r hr q = sourceHillSpectrum t ht v := by
  unfold sourceHillSpectrum
  rw [sourceComplexHminusOne_eq_of_distribution_eq r t hr ht q v h]

/-- Every finite full-domain root-chain level is unchanged across endpoint orders. -/
theorem sourceHillRootSpace_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) (z : ℂ) (n : ℕ) :
    singularHillRootSpace (sourceComplexHminusOne r hr q) z n =
      singularHillRootSpace (sourceComplexHminusOne t ht v) z n := by
  rw [sourceComplexHminusOne_eq_of_distribution_eq r t hr ht q v h]

/-- The full physical algebraic root space is unchanged, including all chains. -/
theorem sourceHillRootSpaceTop_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) (z : ℂ) :
    singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z =
      singularHillRootSpaceTop (sourceComplexHminusOne t ht v) z := by
  rw [sourceComplexHminusOne_eq_of_distribution_eq r t hr ht q v h]

/-- Actual physical algebraic multiplicity is independent of the predual order. -/
theorem sourceHillAlgebraicMultiplicity_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) (z : ℂ) :
    sourceHillAlgebraicMultiplicity r hr q z = sourceHillAlgebraicMultiplicity t ht v z := by
  change Module.finrank ℂ (singularHillRootSpaceTop (sourceComplexHminusOne r hr q) z) =
    Module.finrank ℂ (singularHillRootSpaceTop (sourceComplexHminusOne t ht v) z)
  rw [sourceHillRootSpaceTop_eq_of_distribution_eq r t hr ht q v h]

/-- The entire canonical ordered enumeration, with every algebraic repetition,
is the same for any two admissible endpoint realizations. No shared cutoff is assumed. -/
theorem sourceHillLabels_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : Potential r) (v : Potential t) (h : q.val.val = v.val.val) :
    sourceHillLabels r hr q = sourceHillLabels t ht v := by
  apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
    (sourceHillLabels_finite_fiber r hr q) (sourceHillLabels_finite_fiber t ht v)
    (monotone_sourceHillLabels r hr q) (monotone_sourceHillLabels t ht v)
  intro x
  rw [sourceHillLabels_global_multiplicity, sourceHillLabels_global_multiplicity]
  exact sourceHillAlgebraicMultiplicity_eq_of_distribution_eq r t hr ht q.val v.val h x

/-- All actual signed canonical gap values agree, including every closed gap
and the zero mode, with the original coefficient/gap normalization retained. -/
theorem sourceCanonicalGapValues_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : Potential r) (v : Potential t) (h : q.val.val = v.val.val) :
    sourceCanonicalGapValues r hr q = sourceCanonicalGapValues t ht v := by
  funext k
  simp only [sourceCanonicalGapValues, sourceHillLabels_eq_of_distribution_eq r t hr ht q v h]

/-- Complex canonical labels retain the source lexicographic order and all
actual multiplicities across endpoint realizations of the same distribution. -/
theorem sourceHillComplexLabels_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) : sourceHillComplexLabels r hr q = sourceHillComplexLabels t ht v := by
  let : LinearOrder ℂ := LinearOrder.lift' NLS.ComplexAnalysis.complexLexKey
    NLS.ComplexAnalysis.complexLexKey_injective
  classical
  apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
    (sourceHillComplexLabels_finite_fiber r hr q) (sourceHillComplexLabels_finite_fiber t ht v)
    (fun i j hij => ordered_sourceHillComplexLabels r hr q i j hij)
    (fun i j hij => ordered_sourceHillComplexLabels t ht v i j hij)
  intro x
  convert (sourceHillComplexLabels_global_multiplicity r hr q x).trans
    ((sourceHillAlgebraicMultiplicity_eq_of_distribution_eq r t hr ht q v h x).trans
      (sourceHillComplexLabels_global_multiplicity t ht v x).symm) using 1 <;>
    apply finsum_congr <;> intro i <;> split_ifs <;> rfl

/-- The complete complex signed gap sequence is intrinsic, without reality or
noncollapsed-gap assumptions. -/
theorem sourceComplexCanonicalGapValues_eq_of_distribution_eq
    (r t : ℝ) (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (v : FourierLebesgueSpace (2:ℝ) (-t) ⊤)
    (h : q.val = v.val) :
    sourceComplexCanonicalGapValues r hr q = sourceComplexCanonicalGapValues t ht v := by
  funext k
  simp only [sourceComplexCanonicalGapValues,
    sourceHillComplexLabels_eq_of_distribution_eq r t hr ht q v h]

/-- The endpoint regularity gain preserves the ENTIRE canonical spectrum and
gap sequence. Constants still precede the input; target membership is derived. -/
theorem source_uniform_endpoint_bootstrap_preserves_spectrum
    (r : ℝ) (hr : AdmissiblePredualOrder r) (t : ℝ) (ht : 0 ≤ t) (htr : t ≤ r)
    (R G : ℝ) (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      (∀ n : ℕ, 1 ≤ n → Weight.sobolev (-t) (n:ℤ)*‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤ G) →
      ∃ v : Potential t, v.val.val = q.val.val ∧ ‖v.val‖ ≤ C ∧
        sourceHillLabels t ⟨ht, lt_of_le_of_lt htr hr.2⟩ v = sourceHillLabels r hr q ∧
        sourceCanonicalGapValues t ⟨ht, lt_of_le_of_lt htr hr.2⟩ v =
          sourceCanonicalGapValues r hr q := by
  obtain ⟨C, hC, hgain⟩ := source_uniform_endpoint_bootstrap r hr t ht htr R G hR hG
  refine ⟨C, hC, fun q hq hgap => ?_⟩
  obtain ⟨v, hv, hvn⟩ := hgain q hq hgap
  exact ⟨v, hv, hvn,
    sourceHillLabels_eq_of_distribution_eq t r ⟨ht, lt_of_le_of_lt htr hr.2⟩ hr v q hv,
    sourceCanonicalGapValues_eq_of_distribution_eq t r ⟨ht, lt_of_le_of_lt htr hr.2⟩ hr v q hv⟩

end NLS.Articles.KdVPseudomeasures
