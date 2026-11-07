import NLS.Articles.DNLSEstimates.SpectralSurface
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Proper projection and connectedness of the actual spectral curve

For any continuous radicand the double-cover projection is proper and
open. A zero gives a singleton fiber. Every nonempty clopen part would
project onto the connected base, so that singleton fiber forces the
whole affine curve to be connected, including nodal spectral curves.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.DNLSEstimates

/-- The actual spectral coordinate, in the inherited subspace topology. -/
def doubleCoverProjection (f : ℂ → ℂ) : doubleCover f → ℂ := fun q => q.val.1

theorem continuous_doubleCoverProjection (f : ℂ → ℂ) :
    Continuous (doubleCoverProjection f) := continuous_fst.comp continuous_subtype_val

/-- A continuous local section exists through every point, including a
branch point. The section only needs continuity at its prescribed base. -/
theorem doubleCoverProjection_local_sections (f : ℂ → ℂ) (hf : Continuous f)
    (q : doubleCover f) :
    ∃ s : ℂ → doubleCover f, ContinuousAt s (doubleCoverProjection f q) ∧
      s (doubleCoverProjection f q) = q ∧ Function.RightInverse s (doubleCoverProjection f) := by
  have hsquare (z : ℂ) : (Complex.sqrt (f z))^2 = f z := by
    have h := Complex.cpow_nat_inv_pow (f z) (by decide : 2 ≠ 0)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  by_cases hw : q.val.2 = 0
  · have hz : f q.val.1 = 0 := by
      have h := q.property
      change q.val.2^2 = f q.val.1 at h
      rw [hw] at h
      simpa using h.symm
    let s : ℂ → doubleCover f := fun z => ⟨(z,Complex.sqrt (f z)),hsquare z⟩
    refine ⟨s,?_,?_,fun _ => rfl⟩
    · apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      have hc : ContinuousAt Complex.sqrt (f q.val.1) := by
        rw [hz]
        exact Complex.continuousAt_sqrt (Or.inl (by simp))
      exact continuousAt_id.prodMk (hc.comp (f := f) hf.continuousAt)
    · apply Subtype.ext
      change (q.val.1,Complex.sqrt (f q.val.1)) = q.val
      apply Prod.ext
      · rfl
      · change Complex.sqrt (f q.val.1) = q.val.2
        rw [hz,hw]
        simp
  · let h : ℂ → ℂ := prescribedSquareRoot f q.val.2
    have hbase : h q.val.1 = q.val.2 := prescribedSquareRoot_base f q.val.2 hw _ q.property.symm
    have hh : ContinuousAt h q.val.1 := by
      have hr : f q.val.1/q.val.2^2 = 1 := by rw [← q.property,div_self (pow_ne_zero 2 hw)]
      have hs : ContinuousAt Complex.sqrt (f q.val.1/q.val.2^2) := by
        rw [hr]
        exact Complex.continuousAt_sqrt (Or.inl (by norm_num))
      exact continuousAt_const.fun_mul (hs.comp
        (f := fun z => f z/q.val.2^2) (hf.continuousAt.div_const _))
    let s : ℂ → doubleCover f := fun z => ⟨(z,h z),prescribedSquareRoot_sq f q.val.2 hw z⟩
    refine ⟨s,?_,?_,fun _ => rfl⟩
    · exact Topology.IsInducing.subtypeVal.continuousAt_iff.mpr (continuousAt_id.prodMk hh)
    · apply Subtype.ext
      exact Prod.ext rfl hbase

/-- The projection is open even at multiple spectral points. -/
theorem isOpenMap_doubleCoverProjection (f : ℂ → ℂ) (hf : Continuous f) :
    IsOpenMap (doubleCoverProjection f) :=
  IsOpenMap.of_sections (doubleCoverProjection_local_sections f hf)

/-- Compact subsets of the base have compact inverse images: the square
relation bounds the fiber coordinate uniformly above the compact set. -/
theorem isProperMap_doubleCoverProjection (f : ℂ → ℂ) (hf : Continuous f) :
    IsProperMap (doubleCoverProjection f) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_doubleCoverProjection f,?_⟩
  intro K hK
  obtain ⟨B,hB⟩ := (hK.image hf).isBounded.exists_norm_le
  let R := |B|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : IsClosed (doubleCover f) := isClosed_eq
    (continuous_snd.fun_pow 2) (hf.comp continuous_fst)
  have he : Subtype.val '' ((doubleCoverProjection f) ⁻¹' K) =
      doubleCover f ∩ Prod.fst ⁻¹' K := by
    ext q
    exact ⟨fun ⟨x,hx,hval⟩ => hval ▸ ⟨x.property,hx⟩,
      fun hq => ⟨⟨q,hq.1⟩,hq.2,rfl⟩⟩
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  rw [he]
  apply (hK.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset
    (hc.inter (hK.isClosed.preimage continuous_fst))
  intro q hq
  refine ⟨hq.2,?_⟩
  have hbound : ‖q.2‖^2 ≤ B := by
    have hb := hB (f q.1) ⟨q.1,hq.2,rfl⟩
    have heq := congrArg norm hq.1
    rw [norm_pow] at heq
    exact heq ▸ hb
  rw [mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg q.2,le_abs_self B,abs_nonneg B]

/-- Any nonempty clopen part of the double cover projects onto the whole
complex plane, because its image is both open and closed. -/
theorem doubleCoverProjection_image_clopen (f : ℂ → ℂ) (hf : Continuous f)
    (S : Set (doubleCover f)) (hS : IsClopen S) (hne : S.Nonempty) :
    doubleCoverProjection f '' S = univ := by
  have ho := isOpenMap_doubleCoverProjection f hf S hS.2
  have hc := (isProperMap_doubleCoverProjection f hf).isClosedMap S hS.1
  rcases isClopen_iff.mp (show IsClopen (doubleCoverProjection f '' S) from ⟨hc,ho⟩) with he | he
  · exact (hne.image _).ne_empty he |>.elim
  · exact he

/-- A singleton fiber forces the entire double cover to be connected.
No simplicity or smoothness assumption is used. -/
theorem connectedSpace_doubleCover_of_zero (f : ℂ → ℂ) (hf : Continuous f)
    (z : ℂ) (hz : f z = 0) : ConnectedSpace (doubleCover f) := by
  have hq : (z,(0 : ℂ)) ∈ doubleCover f := by change (0 : ℂ)^2 = f z; rw [hz]; norm_num
  let q : doubleCover f := ⟨(z,0),hq⟩
  have hfiber (x : doubleCover f) (hx : doubleCoverProjection f x = z) : x = q := by
    apply Subtype.ext
    refine Prod.ext hx ?_
    have he := x.property
    change x.val.2^2 = f x.val.1 at he
    rw [show x.val.1 = z from hx,hz] at he
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp he
  apply connectedSpace_iff_clopen.mpr
  refine ⟨⟨q⟩,?_⟩
  intro S hS
  by_cases hne : S.Nonempty
  · right
    apply eq_univ_of_forall
    intro x
    by_contra hx
    have hcompl : Sᶜ.Nonempty := ⟨x,hx⟩
    obtain ⟨a,ha,haq⟩ := (doubleCoverProjection_image_clopen f hf S hS hne).symm ▸ mem_univ z
    obtain ⟨b,hb,hbq⟩ := (doubleCoverProjection_image_clopen f hf Sᶜ hS.compl hcompl).symm ▸ mem_univ z
    rw [hfiber a haq] at ha
    rw [hfiber b hbq] at hb
    exact hb ha
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

/-- Every actual affine spectral curve is connected, including sources
with collapsed gaps and multiple spectral points. -/
theorem spectralCurve_connected {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) : ConnectedSpace (spectralCurve hp a) := by
  let f : ℂ → ℂ := fun z => (canonicalDiscriminant hp (periodOnePotential a) z)^2-4
  have hf : Continuous f :=
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a)).continuous.pow 2).sub continuous_const
  let z := canonicalPeriodicLeft hp hp1 (periodOnePotential a) (periodOnePotential_mem a) 0
  have hz : f z = 0 := by
    apply sub_eq_zero.mpr
    exact (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem a) z).mpr
      (canonicalPeriodicEndpoints_mem_spectrum hp hp1 _ (periodOnePotential_mem a) 0).1
  exact connectedSpace_doubleCover_of_zero f hf z hz

end NLS.Articles.DNLSEstimates
