import NLS.Articles.KdVPseudomeasures.WeightedWeakStarEndpoint
import NLS.SequenceSpaces.SobolevFullDuality
import Mathlib.Topology.Metrizable.Basic

/-!
# Appendix B: weighted weak-star compactness

The parameter `r` below is the regularity of the Wiener *predual*.
Thus the dual coefficients have regularity `-r`. All results hold for every
real r, independently of the narrower KdV regularity range.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- The full physical dual identification, with parameter equal to the
predual order (the coefficients have order `-r`). -/
def wienerDualRealization (r : ℝ) (a : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) :=
  StrongDual.toWeakDual (sobolevDualityIsometry r (by simp) a)

/-- Raw coefficients of an arbitrary weak-star functional, recovered by finite
Wiener tests. This uses full duality, not a representation hypothesis. -/
def weakStarCoordinates (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) : ℂ :=
  f (ofFinsupp (Weight.sobolev r) 1 (Finsupp.single (-n) 1))

theorem continuous_weakStarCoordinates (r : ℝ) : Continuous (weakStarCoordinates r) := by
  apply continuous_pi
  intro n
  exact WeakDual.eval_continuous _

theorem weakStarCoordinates_injective (r : ℝ) : Function.Injective (weakStarCoordinates r) := by
  intro f g h
  apply (WeakDual.toStrongDual (𝕜 := ℂ)).injective
  apply (sobolevDualityIsometry (p := 1) (q := ⊤) r (by simp)).symm.injective
  apply Subtype.ext
  funext n
  simp only [sobolevDualityIsometry_symm_apply]
  exact (sobolevCotangent_val (q := ⊤) r (by simp) f.toStrongDual n).trans
    ((congrFun h n).trans (sobolevCotangent_val (q := ⊤) r (by simp) g.toStrongDual n).symm)

/-- Compact sets in this weighted weak dual are metrizable, using the
countable family of Fourier tests rather than an assumed separability instance. -/
theorem metrizable_weakStar_compact (r : ℝ)
    (K : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hK : IsCompact K) : TopologicalSpace.MetrizableSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun x : K => weakStarCoordinates r x.val) :=
    (continuous_weakStarCoordinates r).comp continuous_subtype_val
  exact (hc.isClosedEmbedding
    ((weakStarCoordinates_injective r).comp Subtype.val_injective)).isEmbedding.metrizableSpace

/-- The actual weighted coefficient norm ball inside the weak-star dual. -/
def weakStarBall (r R : ℝ) : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R

/-- The realization takes a coefficient norm ball onto the entire dual norm ball. -/
theorem image_wienerDualRealization_closedBall (r R : ℝ) :
    wienerDualRealization r '' Metric.closedBall 0 R = weakStarBall r R := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [weakStarBall, wienerDualRealization, Metric.mem_closedBall,
      dist_zero_right] using ha
  · intro hf
    let e := sobolevDualityIsometry (p := 1) (q := ⊤) r (by simp)
    refine ⟨e.symm f.toStrongDual, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      simpa [weakStarBall, Metric.mem_closedBall, dist_zero_right] using hf
    · change StrongDual.toWeakDual (e (e.symm f.toStrongDual)) = f
      rw [LinearIsometryEquiv.apply_symm_apply, WeakDual.toWeakDual_toStrongDual]

/-- Appendix B.1(i): Banach-Alaoglu for every weighted endpoint norm ball. -/
theorem isCompact_weakStarBall (r R : ℝ) : IsCompact (weakStarBall r R) :=
  WeakDual.isCompact_closedBall 0 R

theorem metrizable_weakStarBall (r R : ℝ) :
    TopologicalSpace.MetrizableSpace (weakStarBall r R) :=
  metrizable_weakStar_compact r _ (isCompact_weakStarBall r R)

/-- Compact weighted weak-star sets are sequentially compact. -/
theorem isSeqCompact_of_isCompact_weakStar (r : ℝ)
    {K : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))}
    (hK : IsCompact K) : IsSeqCompact K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let := metrizable_weakStar_compact r K hK
  simpa only [Subtype.range_coe] using
    IsSeqCompact.range (f := fun x : K => x.val) continuous_subtype_val.seqContinuous

theorem isSeqCompact_weakStarBall (r R : ℝ) : IsSeqCompact (weakStarBall r R) :=
  isSeqCompact_of_isCompact_weakStar r (isCompact_weakStarBall r R)

/-- Appendix B.1(iii)(a)-(c): norm-boundedness plus actual weak-star closedness
is equivalent to weak-star compactness. -/
theorem isCompact_weakStar_iff_bounded_closed (r : ℝ)
    (K : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))) :
    IsCompact K ↔ Bornology.IsBounded K ∧ IsClosed K := by
  constructor
  · intro hK
    exact ⟨WeakDual.isBounded_iff_isVonNBounded.mpr (hK.isVonNBounded ℂ), hK.isClosed⟩
  · rintro ⟨hb, hc⟩
    exact WeakDual.isCompact_of_bounded_of_closed hb hc

/-- Weak-star convergent sequences are norm bounded; this is a sequential
statement and does not assert global boundedness of arbitrary convergent nets. -/
theorem isBounded_range_of_weakStar_tendsto (r : ℝ)
    (x : ℕ → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (a : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (h : Tendsto x atTop (𝓝 a)) : Bornology.IsBounded (range x) :=
  WeakDual.isBounded_iff_isVonNBounded.mpr (h.isVonNBounded_range ℂ)

/-- Fourier coordinates induce exactly the weak-star topology on every
norm-bounded subset. This is an equality of induced topologies, expressed as
an embedding, and hence controls arbitrary filters, not just sequences. -/
theorem isEmbedding_weakStarCoordinates_on_bounded (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    Topology.IsEmbedding (fun x : A => weakStarCoordinates r x.val) := by
  let K := closure A
  have hK : IsCompact K := WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure hb) isClosed_closure
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heK := ((continuous_weakStarCoordinates r).comp
    (continuous_subtype_val (p := fun x => x ∈ K))).isClosedEmbedding
      ((weakStarCoordinates_injective r).comp Subtype.val_injective)
  let j : A → K := fun x => ⟨x.val, subset_closure x.property⟩
  have hej : Topology.IsEmbedding j :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp Topology.IsEmbedding.subtypeVal
  exact heK.isEmbedding.comp hej

/-- All bounded subsets, whether closed or not, are weak-star metrizable. -/
theorem metrizable_weakStar_bounded (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) : TopologicalSpace.MetrizableSpace A :=
  (isEmbedding_weakStarCoordinates_on_bounded r A hb).metrizableSpace

/-- Bounded-set coordinate convergence criterion for arbitrary filters. -/
theorem tendsto_weakStar_subtype_iff_coordinates (r : ℝ)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) {α : Type*} {l : Filter α}
    (x : α → A) (a : A) :
    Tendsto x l (𝓝 a) ↔ ∀ n : ℤ,
      Tendsto (fun k => weakStarCoordinates r (x k).val n) l
        (𝓝 (weakStarCoordinates r a.val n)) := by
  rw [(isEmbedding_weakStarCoordinates_on_bounded r A hb).tendsto_nhds_iff]
  exact tendsto_pi_nhds

/-- Uniform boundedness applied to sequentially compact sets in the weak dual. -/
theorem isBounded_of_isSeqCompact_weakStar (r : ℝ)
    {K : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))}
    (hK : IsSeqCompact K) : Bornology.IsBounded K := by
  have hpt (b : WeightedCoeff (Weight.sobolev r) 1) :
      ∃ C, ∀ f : K, ‖f.val b‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((hK.image (WeakDual.eval_continuous b).seqContinuous).isCompact).isBounded.exists_norm_le
    exact ⟨C, fun f => hC _ ⟨f.val, f.property, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun f : K => f.val.toStrongDual) hpt
  rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded]
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  intro f hf
  exact hC ⟨StrongDual.toWeakDual f, hf⟩

/-- Appendix B.1(iii)(a)-(b), with boundedness derived rather than assumed. -/
theorem isCompact_weakStar_iff_isSeqCompact (r : ℝ)
    (K : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))) :
    IsCompact K ↔ IsSeqCompact K := by
  constructor
  · exact isSeqCompact_of_isCompact_weakStar r
  · intro hK
    have hb := isBounded_of_isSeqCompact_weakStar r hK
    have he := isEmbedding_weakStarCoordinates_on_bounded r K hb
    have hc := (hK.image (continuous_weakStarCoordinates r).seqContinuous).isCompact
    have hu : IsCompact (Set.univ : Set K) := he.isCompact_iff.mpr (by
      rw [Set.image_univ]
      change IsCompact (Set.range (weakStarCoordinates r ∘ (Subtype.val : K → _)))
      rw [Set.range_comp, Subtype.range_coe]
      exact hc)
    simpa only [Set.image_univ, Subtype.range_coe] using hu.image continuous_subtype_val

/-- Bounded ambient families satisfy the coefficient criterion for every filter. -/
theorem tendsto_weakStar_iff_coordinates_of_bounded (r : ℝ)
    {α : Type*} {l : Filter α}
    (x : α → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (a : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (hb : Bornology.IsBounded (range x)) :
    Tendsto x l (𝓝 a) ↔ ∀ n : ℤ,
      Tendsto (fun k => weakStarCoordinates r (x k) n) l (𝓝 (weakStarCoordinates r a n)) := by
  let A := insert a (range x)
  have hA : Bornology.IsBounded A := hb.insert a
  let y : α → A := fun k => ⟨x k, mem_insert_of_mem _ ⟨k,rfl⟩⟩
  let b : A := ⟨a, mem_insert _ _⟩
  constructor
  · intro h n
    exact (WeakDual.eval_continuous _).tendsto a |>.comp h
  · intro h
    have hy : Tendsto y l (𝓝 b) :=
      (tendsto_weakStar_subtype_iff_coordinates r A hA y b).mpr h
    exact continuous_subtype_val.tendsto b |>.comp hy

/-- Appendix B.1(ii)(a)-(b), including the norm-boundedness conclusion for
convergent sequences. Arbitrary convergent nets need not have bounded ranges. -/
theorem tendsto_weakStar_seq_iff_bounded_coordinates (r : ℝ)
    (x : ℕ → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (a : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    Tendsto x atTop (𝓝 a) ↔ Bornology.IsBounded (range x) ∧ ∀ n : ℤ,
      Tendsto (fun k => weakStarCoordinates r (x k) n) atTop (𝓝 (weakStarCoordinates r a n)) := by
  constructor
  · intro h
    have hb := isBounded_range_of_weakStar_tendsto r x a h
    exact ⟨hb, (tendsto_weakStar_iff_coordinates_of_bounded r x a hb).mp h⟩
  · rintro ⟨hb, hc⟩
    exact (tendsto_weakStar_iff_coordinates_of_bounded r x a hb).mpr hc

/-- The dual realization recovers exactly the raw coefficient, with the
physical Fourier-index reversal already included in its definition. -/
@[simp] theorem weakStarCoordinates_wienerDualRealization (r : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-r)) ⊤) (n : ℤ) :
    weakStarCoordinates r (wienerDualRealization r a) n = a.val n := by
  change sobolevBilinearPairing r
    (ofFinsupp (Weight.sobolev r) 1 (Finsupp.single (-n) 1)) a = _
  simp [sobolevBilinearPairing_apply, ofFinsupp_apply, Finsupp.single_apply]

/-- The source's real, mean-zero sequence space, realized in the actual
weighted weak dual. The reality condition is conjugate Fourier symmetry. -/
def realMeanZeroWeakStar (r : ℝ) :
    Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :=
  {f | weakStarCoordinates r f 0 = 0 ∧ ∀ n : ℤ,
    weakStarCoordinates r f (-n) = star (weakStarCoordinates r f n)}

theorem isClosed_realMeanZeroWeakStar (r : ℝ) : IsClosed (realMeanZeroWeakStar r) := by
  have hc (n : ℤ) : Continuous (fun f => weakStarCoordinates r f n) :=
    (continuous_apply n).comp (continuous_weakStarCoordinates r)
  convert (isClosed_eq (hc 0) (continuous_const : Continuous (fun _ : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) => (0:ℂ)))).inter
    (isClosed_iInter fun n => isClosed_eq (hc (-n)) (hc n).star) using 1
  ext f
  simp [realMeanZeroWeakStar]

/-- Appendix B.1(i) on the actual real mean-zero endpoint space. -/
theorem isCompact_realMeanZeroWeakStarBall (r R : ℝ) :
    IsCompact (weakStarBall r R ∩ realMeanZeroWeakStar r) :=
  (isCompact_weakStarBall r R).inter_right (isClosed_realMeanZeroWeakStar r)

theorem metrizable_realMeanZeroWeakStarBall (r R : ℝ) :
    TopologicalSpace.MetrizableSpace ↥(weakStarBall r R ∩ realMeanZeroWeakStar r) :=
  metrizable_weakStar_compact r _ (isCompact_realMeanZeroWeakStarBall r R)

theorem isSeqCompact_realMeanZeroWeakStarBall (r R : ℝ) :
    IsSeqCompact (weakStarBall r R ∩ realMeanZeroWeakStar r) :=
  isSeqCompact_of_isCompact_weakStar r (isCompact_realMeanZeroWeakStarBall r R)

end NLS.WeightedCoeff
