import NLS.SequenceSpaces.WeightedWeakStarCompactness
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.DominatedConvergence
import Mathlib.Topology.CompactOpen

/-! # Appendix B: lower weighted norm topology at the exact strict threshold -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The lower weighted norm embedding retains every raw coefficient. -/
def endpointLowerInclusion (s t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (s-t)*p.toReal) :
    WeightedCoeff (Weight.sobolev s) ⊤ →L[ℂ] WeightedCoeff (Weight.sobolev t) p :=
  sobolevHolderInclusion (p := ⊤) (r := p) (q := p) s t hp h

@[simp] theorem endpointLowerInclusion_apply (s t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (s-t)*p.toReal) (a : WeightedCoeff (Weight.sobolev s) ⊤) (n : ℤ) :
    (endpointLowerInclusion s t hp h a).val n = a.val n :=
  sobolevHolderInclusion_apply s t hp h a n

/-- Bounded coefficient convergence implies lower weighted norm convergence,
for arbitrary filters, at precisely the source's summability threshold. -/
theorem tendsto_lowerInclusion_of_bounded_coefficients
    (s t : ℝ) (hp : p ≠ ⊤) (h : 1 < (s-t)*p.toReal)
    {α : Type*} {l : Filter α}
    (x : α → WeightedCoeff (Weight.sobolev s) ⊤)
    (a : WeightedCoeff (Weight.sobolev s) ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => (x k).val n) l (𝓝 (a.val n))) :
    Tendsto (fun k => endpointLowerInclusion s t hp h (x k)) l
      (𝓝 (endpointLowerInclusion s t hp h a)) := by
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  let C := max M 0 + ‖a‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let d : Coeff p := ⟨fun n => (Weight.sobolev (s-t) n : ℂ)⁻¹,
    Weight.inverse_sobolev_memlp
      (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp) h⟩
  let e := weightIsometry (Weight.sobolev t) p
  let y (k : α) := e (endpointLowerInclusion s t hp h (x k - a))
  have heq (k : α) (n : ℤ) : y k n =
      weightEquiv (Weight.sobolev s) ⊤ (x k-a) n * d n := by
    change (Weight.sobolev t n : ℂ) * (endpointLowerInclusion s t hp h (x k-a)).val n =
      ((Weight.sobolev s n : ℂ) * (x k-a).val n) * (Weight.sobolev (s-t) n : ℂ)⁻¹
    rw [endpointLowerInclusion_apply, ← Weight.sobolev_ratio s t n]
    have hw := (Weight.sobolev s).complex_ne_zero n
    field_simp [hw]
  have hy : Tendsto y l (𝓝 0) := by
    apply Coeff.tendsto_zero_of_dominated hp y ((C:ℂ) • d)
    · apply Eventually.of_forall
      intro k n
      rw [heq, norm_mul]
      change _ ≤ ‖(C:ℂ)*d n‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0) _ n).trans
      change ‖x k-a‖ ≤ C
      exact (norm_sub_le _ _).trans (add_le_add
        ((hM _ ⟨k,rfl⟩).trans (le_max_left M 0)) le_rfl)
    · intro n
      have hz : Tendsto (fun k => (x k-a).val n) l (𝓝 0) := by
        simpa using (hc n).sub_const (a.val n)
      change Tendsto (fun k => (Weight.sobolev t n : ℂ) *
        (endpointLowerInclusion s t hp h (x k-a)).val n) l (𝓝 0)
      simpa only [endpointLowerInclusion_apply, mul_zero] using
        hz.const_mul (Weight.sobolev t n : ℂ)
  have ht := e.symm.continuous.tendsto 0 |>.comp hy
  have ht' : Tendsto (fun k => endpointLowerInclusion s t hp h (x k) -
      endpointLowerInclusion s t hp h a) l (𝓝 0) := by
    change Tendsto (fun k => e.symm (e (endpointLowerInclusion s t hp h (x k-a))))
      l (𝓝 (e.symm 0)) at ht
    simpa only [LinearIsometryEquiv.symm_apply_apply, map_sub, map_zero] using ht
  exact tendsto_sub_nhds_zero_iff.mp ht'

/-- The full coefficient representative supplied by existing duality. -/
def weakStarCoeff (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    WeightedCoeff (Weight.sobolev (-r)) ⊤ :=
  sobolevCotangent r (by simp) f.toStrongDual

@[simp] theorem weakStarCoeff_val (r : ℝ)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) :
    (weakStarCoeff r f).val n = weakStarCoordinates r f n :=
  sobolevCotangent_val r (by simp) f.toStrongDual n

/-- The lower norm realization of the actual weak-star functional. -/
def lowerWeakStarRealization (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    WeightedCoeff (Weight.sobolev t) p :=
  endpointLowerInclusion (-r) t hp h (weakStarCoeff r f)

@[simp] theorem lowerWeakStarRealization_val (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) :
    (lowerWeakStarRealization r t hp h f).val n = weakStarCoordinates r f n := by
  simp only [lowerWeakStarRealization, endpointLowerInclusion_apply, weakStarCoeff_val]

theorem lowerWeakStarRealization_injective (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal) :
    Function.Injective (lowerWeakStarRealization r t hp h) := by
  intro f g hfg
  apply weakStarCoordinates_injective r
  funext n
  simpa only [lowerWeakStarRealization_val] using
    congrArg (fun a : WeightedCoeff (Weight.sobolev t) p => a.val n) hfg

/-- Lower norm convergence holds continuously over a common
bounded domain; no compactness of that domain is assumed. -/
theorem continuous_lowerWeakStarRealization_on_bounded (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    Continuous (fun x : A => lowerWeakStarRealization r t hp h x.val) := by
  have hcb : Bornology.IsBounded (range (fun x : A => weakStarCoeff r x.val)) := by
    obtain ⟨M, hM⟩ :=
      (WeakDual.isBounded_toWeakDual_preimage_iff_isBounded.mpr hb).exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M, ?_⟩
    rintro _ ⟨f, rfl⟩
    change ‖sobolevCotangent (q := ⊤) r (by simp) f.val.toStrongDual‖ ≤ M
    rw [norm_sobolevCotangent]
    exact hM _ f.property
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_lowerInclusion_of_bounded_coefficients (-r) t hp h
    (fun x : A => weakStarCoeff r x.val) (weakStarCoeff r a.val) hcb
  intro n
  simp only [weakStarCoeff_val]
  exact ((WeakDual.eval_continuous _).comp continuous_subtype_val).continuousAt

/-- Appendix B.1(iv): on any norm-bounded set, the lower weighted norm and
weak-star induced topologies coincide. Here source order is `s=-r`, target
order is `t`, and the exact condition is `(s-t)*p>1`, with finite `p>=1`. -/
theorem isEmbedding_lowerWeakStarRealization_on_bounded (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    Topology.IsEmbedding (fun x : A => lowerWeakStarRealization r t hp h x.val) := by
  have hg : Continuous (fun y : WeightedCoeff (Weight.sobolev t) p => y.val) := by
    apply continuous_pi
    intro n
    exact (evalCLM (Weight.sobolev t) p n).continuous
  apply Topology.IsEmbedding.of_comp
    (continuous_lowerWeakStarRealization_on_bounded r t hp h A hb) hg
  have heq : ((fun y : WeightedCoeff (Weight.sobolev t) p => y.val) ∘
      (fun x : A => lowerWeakStarRealization r t hp h x.val)) =
      (fun x : A => weakStarCoordinates r x.val) := by
    funext x n
    exact lowerWeakStarRealization_val r t hp h x.val n
  rw [heq]
  exact isEmbedding_weakStarCoordinates_on_bounded r A hb

/-- Appendix B.1(iii)(a)-(d): for a bounded set, weak-star compactness is
equivalent to compactness of the actual lower weighted norm image. -/
theorem isCompact_iff_lowerWeakStarRealization_image (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    IsCompact A ↔ IsCompact (lowerWeakStarRealization r t hp h '' A) := by
  have he := isEmbedding_lowerWeakStarRealization_on_bounded r t hp h A hb
  have heq : (fun x : A => lowerWeakStarRealization r t hp h x.val) '' univ =
      lowerWeakStarRealization r t hp h '' A := by
    rw [Set.image_univ]
    change range (lowerWeakStarRealization r t hp h ∘ (Subtype.val : A → _)) = _
    rw [Set.range_comp, Subtype.range_coe]
  constructor
  · intro hA
    have hu : IsCompact (univ : Set A) := by
      let : CompactSpace A := isCompact_iff_compactSpace.mp hA
      exact isCompact_univ
    rw [← heq]
    exact he.isCompact_iff.mp hu
  · intro hA
    have hu : IsCompact (univ : Set A) := he.isCompact_iff.mpr (heq.symm ▸ hA)
    simpa only [Set.image_univ, Subtype.range_coe] using hu.image continuous_subtype_val

/-- Appendix B.1(ii)(a)-(c), for each admissible lower norm. -/
theorem tendsto_weakStar_seq_iff_bounded_lower (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (x : ℕ → WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))
    (a : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    Tendsto x atTop (𝓝 a) ↔ Bornology.IsBounded (range x) ∧
      Tendsto (fun k => lowerWeakStarRealization r t hp h (x k)) atTop
        (𝓝 (lowerWeakStarRealization r t hp h a)) := by
  constructor
  · intro hx
    have hb := isBounded_range_of_weakStar_tendsto r x a hx
    let A := insert a (range x)
    let y : ℕ → A := fun k => ⟨x k, mem_insert_of_mem _ ⟨k,rfl⟩⟩
    let b : A := ⟨a, mem_insert _ _⟩
    have hy : Tendsto y atTop (𝓝 b) := by
      apply Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff.mpr
      exact hx
    refine ⟨hb, ?_⟩
    have hc : Continuous (fun z : A => lowerWeakStarRealization (p := p) r t hp h z.val) :=
      continuous_lowerWeakStarRealization_on_bounded r t hp h A (hb.insert a)
    change Tendsto ((fun z : A => lowerWeakStarRealization (p := p) r t hp h z.val) ∘ y)
      atTop (𝓝 (lowerWeakStarRealization (p := p) r t hp h b.val))
    exact (hc.tendsto b).comp hy
  · rintro ⟨hb, ht⟩
    apply (tendsto_weakStar_iff_coordinates_of_bounded r x a hb).mpr
    intro n
    have hc := (evalCLM (Weight.sobolev t) p n).continuous.tendsto
      (lowerWeakStarRealization r t hp h a) |>.comp ht
    simpa only [Function.comp_def, evalCLM_apply, lowerWeakStarRealization_val] using hc

/-- The full compactness characterization retains boundedness as a conclusion
in the forward direction and a required conjunct in the reverse direction. -/
theorem isCompact_weakStar_iff_bounded_lower_compact (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))) :
    IsCompact A ↔ Bornology.IsBounded A ∧
      IsCompact (lowerWeakStarRealization r t hp h '' A) := by
  constructor
  · intro hA
    have hb := (isCompact_weakStar_iff_bounded_closed r A).mp hA |>.1
    exact ⟨hb, (isCompact_iff_lowerWeakStarRealization_image r t hp h A hb).mp hA⟩
  · rintro ⟨hb, hc⟩
    exact (isCompact_iff_lowerWeakStarRealization_image r t hp h A hb).mpr hc

/-- Lower realization on a norm-bounded weak-star subset, as a continuous map. -/
def lowerWeakStarMapOn (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V) : C(V, WeightedCoeff (Weight.sobolev t) p) :=
  ⟨fun f => lowerWeakStarRealization r t hp h f.val,
    continuous_lowerWeakStarRealization_on_bounded r t hp h V hb⟩

/-- The lower norm realization induces exactly the compact-open weak-star
trajectory topology, rather than merely its pointwise evaluations. -/
theorem isEmbedding_lowerWeakStarTrajectory (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V) {K : Type*} [TopologicalSpace K] :
    Topology.IsEmbedding ((lowerWeakStarMapOn r t hp h V hb).comp :
      C(K,V) → C(K, WeightedCoeff (Weight.sobolev t) p)) :=
  ContinuousMap.isEmbedding_postcomp _
    (isEmbedding_lowerWeakStarRealization_on_bounded r t hp h V hb)

/-- Continuous dependence in the lower norm trajectory space is equivalent
to continuous dependence in the endpoint weak-star trajectory space. -/
theorem continuous_weakStarTrajectory_iff_lower (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V)
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    (S : X → C(K,V)) :
    Continuous S ↔ Continuous (fun x => (lowerWeakStarMapOn r t hp h V hb).comp (S x)) :=
  (isEmbedding_lowerWeakStarTrajectory r t hp h V hb).continuous_iff

end NLS.WeightedCoeff
