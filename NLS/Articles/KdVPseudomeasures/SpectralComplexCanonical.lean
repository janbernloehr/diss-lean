import NLS.Articles.KdVPseudomeasures.SpectralComplexUniqueness
import NLS.Articles.KdVPseudomeasures.SpectralCanonicalLabels

/-! Canonical complex spectral labels in the source order, independent of every choice. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV NLS.ComplexAnalysis

/-- An admissible actual global-label cutoff obtained from the proved original complex norm ball. -/
def sourceHillComplexLabelCutoff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ℕ :=
  Classical.choose (source_uniform_complex_labeling r hr ‖q‖)

theorem sourceHillComplexLabelCutoff_spec (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    2 ≤ sourceHillComplexLabelCutoff r hr q ∧
      ∃ ell : ℕ → ℂ, SourceHillComplexLabeling r hr q (sourceHillComplexLabelCutoff r hr q) ell := by
  have h := Classical.choose_spec (source_uniform_complex_labeling r hr ‖q‖)
  exact ⟨h.1, h.2 q le_rfl⟩

/-- The intrinsic entire original complex spectrum, repeated by actual physical algebraic multiplicity. -/
def sourceHillComplexLabels (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : ℕ → ℂ :=
  Classical.choose (sourceHillComplexLabelCutoff_spec r hr q).2

theorem sourceHillComplexLabels_spec (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    SourceHillComplexLabeling r hr q (sourceHillComplexLabelCutoff r hr q) (sourceHillComplexLabels r hr q) :=
  Classical.choose_spec (sourceHillComplexLabelCutoff_spec r hr q).2

/-- Every actual physical labeling is the same canonical one, regardless of its cutoff. -/
theorem sourceHillComplexLabels_eq_of_labeling (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ) (ell : ℕ → ℂ)
    (h : SourceHillComplexLabeling r hr q N ell) : ell = sourceHillComplexLabels r hr q :=
  h.unique (sourceHillComplexLabels_spec r hr q)

/-- The source's lexicographic order is real part first, imaginary part second. -/
theorem ordered_sourceHillComplexLabels (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (i j : ℕ) (hij : i ≤ j) :
    complexLexLE (sourceHillComplexLabels r hr q i) (sourceHillComplexLabels r hr q j) :=
  (sourceHillComplexLabels_spec r hr q).monotone i j hij

/-- The canonical enumeration exhausts the full actual original complex spectrum. -/
theorem sourceHillComplexLabels_spectrum_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    z ∈ sourceHillSpectrum r hr q ↔ ∃ j : ℕ, z = sourceHillComplexLabels r hr q j :=
  (sourceHillComplexLabels_spec r hr q).spectrum z

theorem sourceHillComplexLabels_finite_fiber (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    {j : ℕ | sourceHillComplexLabels r hr q j = z}.Finite :=
  (sourceHillComplexLabels_spec r hr q).finite_fiber z

/-- Globally, repetitions are exactly the dimensions of the full original algebraic root spaces. -/
theorem sourceHillComplexLabels_global_multiplicity (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    (∑ᶠ j : ℕ, if sourceHillComplexLabels r hr q j = z then (1:ℕ) else 0) =
      sourceHillAlgebraicMultiplicity r hr q z :=
  ((sourceHillComplexLabels_spec r hr q).finite_support_and_multiplicity z).2

/-- Any intrinsic high pair appears in exactly the corresponding odd/even canonical slots. -/
theorem sourceHillComplexLabels_eq_pair (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (N : ℕ)
    (h : SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q))
    (n : ℕ) (hn : N ≤ n) (p : SourceHillComplexPair r hr q n) :
    sourceHillComplexLabels r hr q (2*n-1) = p.left ∧
      sourceHillComplexLabels r hr q (2*n) = p.right := by
  obtain ⟨s, hl, hrr⟩ := h.high_pair n hn
  have he := SourceHillComplexPair.unique r hr q n s p
  simpa only [he] using And.intro hl hrr

/-- The first slot is an actual lexicographically least spectral value; no simplicity is asserted. -/
theorem sourceHillComplexLabels_zero_least (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceHillComplexLabels r hr q 0 ∈ sourceHillSpectrum r hr q ∧
      ∀ z ∈ sourceHillSpectrum r hr q, complexLexLE (sourceHillComplexLabels r hr q 0) z := by
  refine ⟨(sourceHillComplexLabels_spec r hr q).spectral 0, ?_⟩
  intro z hz
  obtain ⟨j, rfl⟩ := (sourceHillComplexLabels_spectrum_iff r hr q z).mp hz
  exact ordered_sourceHillComplexLabels r hr q 0 j (Nat.zero_le j)

/-- One original complex norm-ball cutoff identifies the SAME intrinsic labels for every potential. -/
theorem source_uniform_canonical_complex_labels (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q) := by
  obtain ⟨N, hN, hc⟩ := source_uniform_complex_labeling r hr R
  refine ⟨N, hN, fun q hq => ?_⟩
  obtain ⟨ell, he⟩ := hc q hq
  have hu := sourceHillComplexLabels_eq_of_labeling r hr q N ell he
  rwa [hu] at he

/-- The existing actual real labeling is literally a physical complex labeling,
with the same slots and full algebraic repetitions. -/
theorem sourceHillComplexLabeling_of_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (N : ℕ) (ell : ℕ → ℝ) (h : SourceHillRealLabeling r hr q N ell) :
    SourceHillComplexLabeling r hr q.val N (fun j => (ell j:ℂ)) := by
  refine ⟨h.cutoff_ge_two, h.cutoff_small, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact (complexLexLE_ofReal_iff (ell i) (ell j)).mpr (h.monotone hij)
  · exact h.spectrum
  · intro n hn
    obtain ⟨p, hl, hrr⟩ := h.high_pair n hn
    refine ⟨EndpointHillRealPair.toComplex r hr.1 hr.2 n (sourceEndpointCoefficients r q.val) p, ?_, ?_⟩
    · exact congrArg Complex.ofReal hl
    · exact congrArg Complex.ofReal hrr
  · intro z
    by_cases hz : z.im = 0
    · have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [hz]
      rw [← he]
      simpa only [Complex.ofReal_inj] using h.central_counts z.re
    · have hout : z ∉ sourceCentralSpectrum r hr q.val N := by
        intro hm
        exact hz (sourceHillSpectrum_ofPotential_real r hr q z
          ((mem_sourceCentralSpectrum r hr q.val N z).mp hm).1)
      rw [if_neg hout]
      apply Finset.sum_eq_zero
      intro j _
      apply if_neg
      intro he
      apply hz
      simpa only [Complex.ofReal_im] using (congrArg Complex.im he).symm
  · exact h.central_below

/-- The canonical complex labels extend the already proved original real labels
pointwise, rather than defining a different real spectral model. -/
theorem sourceHillComplexLabels_ofPotential (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    sourceHillComplexLabels r hr q.val = fun j => (sourceHillLabels r hr q j:ℂ) := by
  exact (sourceHillComplexLabels_eq_of_labeling r hr q.val (sourceHillLabelCutoff r hr q) _
    (sourceHillComplexLabeling_of_real r hr q _ _ (sourceHillLabels_spec r hr q))).symm

/-- The common canonical cutoff retains the ORIGINAL norm-radius contraction,
so it works simultaneously for all stronger spectral weights as well. -/
theorem source_uniform_canonical_complex_labels_with_contraction (r : ℝ)
    (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧
      (∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*R ≤ 1/2) ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
        SourceHillComplexLabeling r hr q N (sourceHillComplexLabels r hr q) := by
  obtain ⟨N, hN, hs, hc⟩ := source_uniform_all_complex_central_counts r hr R
  refine ⟨N, hN, hs, fun q hq => ?_⟩
  have hsmall (n : ℕ) (hn : N ≤ n) : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq (by positivity [endpointHillConstant_pos r hr.2])).trans (hs n hn)
  obtain ⟨ell, hm, hsp, hp, hcnt, hb⟩ := exists_sourceHillComplexLabels r hr q N hN hsmall (hc q hq N le_rfl)
  have he : SourceHillComplexLabeling r hr q N ell := ⟨hN, hsmall, hm, hsp, hp, hcnt, hb⟩
  have hu := sourceHillComplexLabels_eq_of_labeling r hr q N ell he
  rwa [hu] at he

end NLS.Articles.KdVPseudomeasures
