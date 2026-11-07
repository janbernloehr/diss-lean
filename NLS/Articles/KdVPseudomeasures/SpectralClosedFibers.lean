import NLS.Articles.KdVPseudomeasures.SpectralLabelContinuity

/-! Closedness and compactness of ACTUAL canonical spectral fibers, with
original endpoint boundedness kept explicit. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- An entire prescribed actual canonical spectrum, including its algebraic repetitions. -/
def sourceCanonicalSpectralFiber (r : ℝ) (hr : AdmissiblePredualOrder r) (ell : ℕ → ℝ) :
    Set (WeakStarPotential r) :=
  {q | sourceHillLabels r hr q.toPotential = ell}

/-- The full canonical spectral fiber is relatively weak-star closed on
EVERY bounded original physical set. -/
theorem isClosed_sourceCanonicalSpectralFiber_on_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) (ell : ℕ → ℝ) :
    IsClosed {q : A | q.val ∈ sourceCanonicalSpectralFiber r hr ell} :=
  isClosed_eq (continuous_sourceHillLabels_sequence_on_bounded r hr A hb) continuous_const

/-- Any specified endpoint bound and complete canonical spectrum give a
weak-star compact family, retaining every physical source constraint. -/
theorem isCompact_sourceNormBall_canonicalSpectralFiber (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (ell : ℕ → ℝ) :
    IsCompact {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R ∧
      q ∈ sourceCanonicalSpectralFiber r hr ell} := by
  let A := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  let : CompactSpace A := isCompact_iff_compactSpace.mp (isCompact_sourceNormBall r R)
  have hc := isClosed_sourceCanonicalSpectralFiber_on_bounded r hr A
    ⟨R, fun _ hq => hq⟩ ell
  have hi := hc.isCompact.image (continuous_subtype_val : Continuous (Subtype.val : A → WeakStarPotential r))
  convert hi using 1
  ext q
  constructor
  · rintro ⟨hq, hl⟩
    exact ⟨⟨q,hq⟩, hl, rfl⟩
  · rintro ⟨⟨v,hv⟩, hl, rfl⟩
    exact ⟨hv, hl⟩

/-- A globally endpoint norm-bounded actual canonical fiber is weak-star
closed in the ENTIRE original physical space. -/
theorem isClosed_sourceCanonicalSpectralFiber_of_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (ell : ℕ → ℝ) (hb : PotentialNormBounded r (sourceCanonicalSpectralFiber r hr ell)) :
    IsClosed (sourceCanonicalSpectralFiber r hr ell) := by
  obtain ⟨R, hR⟩ := hb
  have he : sourceCanonicalSpectralFiber r hr ell =
      {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R ∧
        q ∈ sourceCanonicalSpectralFiber r hr ell} := by
    ext q
    exact ⟨fun hq => ⟨hR q hq, hq⟩, fun hq => hq.2⟩
  rw [he]
  exact ((isCompact_source_iff_bounded_closed r _).mp
    (isCompact_sourceNormBall_canonicalSpectralFiber r hr R ell)).2

/-- For an ENTIRE actual canonical spectral fiber, endpoint norm boundedness
is exactly weak-star compactness. Boundedness is not assumed to follow from
the spectrum by this topological theorem. -/
theorem isCompact_sourceCanonicalSpectralFiber_iff_bounded (r : ℝ) (hr : AdmissiblePredualOrder r)
    (ell : ℕ → ℝ) :
    IsCompact (sourceCanonicalSpectralFiber r hr ell) ↔
      PotentialNormBounded r (sourceCanonicalSpectralFiber r hr ell) := by
  constructor
  · intro hc
    exact ((isCompact_source_iff_bounded_closed r _).mp hc).1
  · intro hb
    exact (isCompact_source_iff_bounded_closed r _).mpr
      ⟨hb, isClosed_sourceCanonicalSpectralFiber_of_bounded r hr ell hb⟩

/-- Every member has the prescribed actual physical spectrum, with no omitted
central eigenvalues or high tail. -/
theorem sourceCanonicalSpectralFiber_spectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (ell : ℕ → ℝ) (q : WeakStarPotential r) (hq : q ∈ sourceCanonicalSpectralFiber r hr ell)
    (z : ℂ) : z ∈ sourceHillSpectrum r hr q.toPotential.val ↔ ∃ j : ℕ, z = (ell j:ℂ) := by
  rw [sourceHillLabels_spectrum_iff, show sourceHillLabels r hr q.toPotential = ell from hq]

/-- The ENTIRE fixed spectrum also fixes every ACTUAL physical algebraic multiplicity. -/
theorem sourceCanonicalSpectralFiber_multiplicity (r : ℝ) (hr : AdmissiblePredualOrder r)
    (ell : ℕ → ℝ) (q : WeakStarPotential r) (hq : q ∈ sourceCanonicalSpectralFiber r hr ell)
    (x : ℝ) : sourceHillAlgebraicMultiplicity r hr q.toPotential.val x =
      ∑ᶠ j : ℕ, if ell j = x then (1:ℕ) else 0 := by
  rw [← sourceHillLabels_global_multiplicity, show sourceHillLabels r hr q.toPotential = ell from hq]

/-- Actual canonical fiber membership is unchanged by an endpoint regularity
reinterpretation of the SAME entire original physical distribution. -/
theorem sourceCanonicalSpectralFiber_cross_order (r t : ℝ)
    (hr : AdmissiblePredualOrder r) (ht : AdmissiblePredualOrder t)
    (q : WeakStarPotential r) (v : WeakStarPotential t)
    (h : q.toPotential.val.val = v.toPotential.val.val) (ell : ℕ → ℝ) :
    q ∈ sourceCanonicalSpectralFiber r hr ell ↔ v ∈ sourceCanonicalSpectralFiber t ht ell := by
  change sourceHillLabels r hr q.toPotential = ell ↔ sourceHillLabels t ht v.toPotential = ell
  rw [sourceHillLabels_eq_of_distribution_eq r t hr ht q.toPotential v.toPotential h]

end NLS.Articles.KdVPseudomeasures
