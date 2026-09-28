import NLS.ZakharovShabat.SourceGapSampleSummability
import NLS.ZakharovShabat.RestoredSpectralPairs
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds
import NLS.SequenceSpaces.PairedTailBounds
import NLS.SequenceSpaces.DeletedCoordinate

/-!
# Tail bounds for deleted roots placed in periodic gaps

Each retained displaced root in a periodic gap is bounded by the
corresponding left endpoint displacement plus the gap length. This
bound persists in every finite `ℓᵖ` tail, uniformly over all choices
of roots inside the gaps. It is the compactness estimate needed in
the continuation argument of Proposition 12.9.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every finite tail of a deleted-root displacement sequence with
roots in their assigned gaps is bounded by the endpoint and gap tails. -/
theorem norm_deletedRoots_sub_truncate_le_gap_tails
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (a : DeletedCoeff p n)
    (hgap : ∀ m : ℤ, m ≠ n →
      displacedRoots (a : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 ψ m)
    (s : Finset ℤ) :
    ‖(a : Coeff p)-Coeff.truncate s (a : Coeff p)‖ ≤
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) -
        Coeff.truncate s (canonicalPeriodicLeftDisplacement hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ))‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ -
        Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 ψ)‖ := by
  apply Coeff.norm_sub_truncate_le_of_pointwise_norm_le_add
    (canonicalPeriodicLeftDisplacement hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ))
    (sourcePeriodicGapDisplacement hp hp1 ψ) (a : Coeff p) s
  intro m _
  by_cases hmn : m = n
  · subst m
    rw [show (a : Coeff p) n = 0 from a.property,norm_zero]
    positivity
  · have hbound := norm_sourcePeriodicSegment_sample_sub_free_le
      hp hp1 ψ m (displacedRoots (a : Coeff p) m) (hgap m hmn)
    simpa only [displacedRoots,add_sub_cancel_left] using hbound

/-- The full deleted-root norm is bounded by the left-endpoint and
gap displacement norms when its retained roots lie in the gaps. -/
theorem norm_deletedRoots_le_gap_displacements
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (a : DeletedCoeff p n)
    (hgap : ∀ m : ℤ, m ≠ n →
      displacedRoots (a : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 ψ m) :
    ‖(a : Coeff p)‖ ≤
      ‖canonicalPeriodicLeftDisplacement hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)‖ +
      ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ := by
  simpa using norm_deletedRoots_sub_truncate_le_gap_tails
    hp hp1 ψ n a hgap ∅

/-- Near any source, all deleted-root sequences placed in their
periodic gaps have uniformly small `ℓᵖ` tails. The bound is uniform
over the choice of root within each gap. -/
theorem exists_uniform_small_deletedGapRoots_tails
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ a : DeletedCoeff p n,
        (∀ m : ℤ, m ≠ n →
          displacedRoots (a : Coeff p) m ∈
            sourcePeriodicSegment hp hp1 ψ m) →
        ∀ M : ℕ, N ≤ M →
          ‖(a : Coeff p)-
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (a : Coeff p)‖ ≤ ε := by
  obtain ⟨N,_,U,hUopen,_,hφU,_,_,_,hdata⟩ :=
    exists_uniform_small_canonicalPeriodicDisplacements
      hp hp1 (periodOnePotential φ) (by positivity : 0 < ε/3)
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  refine ⟨N,V,hUopen.preimage (periodOnePotential (p := p)).continuous,hφU,?_⟩
  intro ψ hψ a hgapRoots M hM
  let s := Finset.Icc (-(M : ℤ)) M
  let L := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R := canonicalPeriodicRightDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let G := sourcePeriodicGapDisplacement hp hp1 ψ
  obtain ⟨_,_,htails⟩ :=
    hdata (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)
  have hL : ‖L-Coeff.truncate s L‖ ≤ ε/3 := (htails M hM).1
  have hR : ‖R-Coeff.truncate s R‖ ≤ ε/3 := (htails M hM).2
  have hGexpr : G-Coeff.truncate s G =
      (R-Coeff.truncate s R)-(L-Coeff.truncate s L) := by
    ext j
    by_cases hj : j ∈ s
    · simp [L,R,G,sourcePeriodicGapDisplacement,Coeff.truncate_apply,hj]
    · simp [L,R,G,sourcePeriodicGapDisplacement,Coeff.truncate_apply,hj]
  have hG : ‖G-Coeff.truncate s G‖ ≤ 2*ε/3 := by
    rw [hGexpr]
    have htri := norm_sub_le (R-Coeff.truncate s R) (L-Coeff.truncate s L)
    linarith
  have ha := norm_deletedRoots_sub_truncate_le_gap_tails
    hp hp1 ψ n a hgapRoots s
  dsimp only [L,G,s] at hL hG ha ⊢
  linarith

end NLS.ZakharovShabat
