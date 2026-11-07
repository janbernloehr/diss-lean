import NLS.Articles.KdVPseudomeasures.SpectralLabelUniqueness

/-! Canonical actual singular spectral labels, independent of every cutoff and enumeration choice. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- A proved admissible cutoff for the original potential, rather than a supplied root list. -/
def sourceHillLabelCutoff (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) : ℕ :=
  Classical.choose (exists_wideEndpointHill_cutoff r hr.2 ‖q.val‖)

theorem sourceHillLabelCutoff_spec (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    2 ≤ sourceHillLabelCutoff r hr q ∧ ∀ n : ℕ, sourceHillLabelCutoff r hr q ≤ n →
      13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2 :=
  Classical.choose_spec (exists_wideEndpointHill_cutoff r hr.2 ‖q.val‖)

/-- The intrinsic one-sided spectrum of the original singular operator, with ACTUAL algebraic repetitions. -/
def sourceHillLabels (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) : ℕ → ℝ :=
  Classical.choose (exists_sourceHillRealLabeling r hr q (sourceHillLabelCutoff r hr q)
    (sourceHillLabelCutoff_spec r hr q).1 (sourceHillLabelCutoff_spec r hr q).2)

theorem sourceHillLabels_spec (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    SourceHillRealLabeling r hr q (sourceHillLabelCutoff r hr q) (sourceHillLabels r hr q) :=
  Classical.choose_spec (exists_sourceHillRealLabeling r hr q (sourceHillLabelCutoff r hr q)
    (sourceHillLabelCutoff_spec r hr q).1 (sourceHillLabelCutoff_spec r hr q).2)

/-- Every admissible central cutoff describes the SAME canonical labels and actual multiplicities. -/
theorem sourceHillLabels_spec_at (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2) :
    SourceHillRealLabeling r hr q N (sourceHillLabels r hr q) := by
  obtain ⟨ell,he⟩ := exists_sourceHillRealLabeling r hr q N hN hs
  have hu := he.unique (sourceHillLabels_spec r hr q)
  rwa [hu] at he

theorem monotone_sourceHillLabels (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    Monotone (sourceHillLabels r hr q) := (sourceHillLabels_spec r hr q).monotone

/-- The canonical enumeration exhausts the ENTIRE actual original physical spectrum. -/
theorem sourceHillLabels_spectrum_iff (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (z : ℂ) :
    z ∈ sourceHillSpectrum r hr q.val ↔ ∃ j : ℕ, z = (sourceHillLabels r hr q j:ℂ) :=
  (sourceHillLabels_spec r hr q).spectrum z

theorem sourceHillLabels_finite_fiber (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (x : ℝ) :
    {j : ℕ | sourceHillLabels r hr q j = x}.Finite := (sourceHillLabels_spec r hr q).finite_fiber x

/-- Canonical repetitions are exactly full original physical algebraic multiplicities, globally. -/
theorem sourceHillLabels_global_multiplicity (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (x : ℝ) :
    (∑ᶠ j : ℕ, if sourceHillLabels r hr q j = x then (1:ℕ) else 0) =
      sourceHillAlgebraicMultiplicity r hr q.val x :=
  ((sourceHillLabels_spec r hr q).finite_support_and_multiplicity x).2

/-- Any actual high pair occupies exactly its usual odd/even canonical slots. -/
theorem sourceHillLabels_eq_pair (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖ ≤ 1/2)
    (n : ℕ) (hn : N ≤ n) (p : SourceHillRealPair r hr q n) :
    sourceHillLabels r hr q (2*n-1) = p.left ∧ sourceHillLabels r hr q (2*n) = p.right := by
  obtain ⟨s,hl,hrr⟩ := (sourceHillLabels_spec_at r hr q N hN hs).high_pair n hn
  have he := SourceHillRealPair.unique r hr q n s p
  simpa only [he] using And.intro hl hrr

/-- The first canonical slot is an actual lowest spectral value. No simplicity assertion is assumed. -/
theorem sourceHillLabels_zero_lowest (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    (sourceHillLabels r hr q 0:ℂ) ∈ sourceHillSpectrum r hr q.val ∧
      ∀ z ∈ sourceHillSpectrum r hr q.val, sourceHillLabels r hr q 0 ≤ z.re := by
  refine ⟨(sourceHillLabels_spec r hr q).spectral 0,?_⟩
  intro z hz
  obtain ⟨j,rfl⟩ := (sourceHillLabels_spectrum_iff r hr q z).mp hz
  exact monotone_sourceHillLabels r hr q (Nat.zero_le j)

/-- One original norm-ball cutoff identifies the same canonical labels for every physical potential. -/
theorem source_uniform_canonical_labels (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : Potential r, ‖q.val‖ ≤ R →
      SourceHillRealLabeling r hr q N (sourceHillLabels r hr q) := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,fun q hq => sourceHillLabels_spec_at r hr q N hN ?_⟩
  intro n hn
  exact (mul_le_mul_of_nonneg_left hq (mul_nonneg
    (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
    (Real.rpow_nonneg (by positivity) _))).trans (hcut n hn)

end NLS.Articles.KdVPseudomeasures
