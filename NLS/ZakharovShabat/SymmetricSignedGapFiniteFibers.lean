import NLS.ZakharovShabat.SymmetricSourceCoordinates
import NLS.SequenceSpaces.RealCoeffTruncation

/-! # Finite-gap reduction of symmetric signed-gap collisions

Finite output support is exactly the actual finite-gap property in the
explicit symmetric Fourier coordinates. If the signed-gap map is open,
every collision produces a collision at finitely supported output. The
openness hypothesis is explicit: the free-source local inverse alone does
not establish it throughout the symmetric slice.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- In symmetric coordinates, actual finite-gap sources are exactly those with finite signed-gap output. -/
theorem symmetricSource_finiteGap_iff_finite_signedGap_support
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : RealCoeff p) :
    symmetricRealSourceCoefficients p a ∈ sourceFiniteGapLocus hp hp1 ↔
      (Function.support (symmetricSourceSignedGapMap hp hp1 a)).Finite := by
  let φ := symmetricRealSourceCoefficients p a
  have hzero (n : ℤ) :
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n = 0 ↔
        symmetricSourceSignedGapMap hp hp1 a n = 0 := by
    have h := abs_sourceSignedGapSequence_re_of_reflection_fixed hp hp1 φ
      (symmetricRealSourceCoefficients_reflection_fixed a) n
    change |symmetricSourceSignedGapMap hp hp1 a n| =
      (canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re at h
    constructor
    · intro hz
      rw [hz,zero_re] at h
      exact abs_eq_zero.mp h
    · intro hz
      rw [hz,abs_zero] at h
      have hi := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
        (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
      apply Complex.ext
      · exact h.symm
      · simp only [canonicalPeriodicGap,sub_im,hi.1,hi.2,sub_self,zero_im]
  change {n | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0}.Finite ↔ _
  have he : {n | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0} =
      Function.support (symmetricSourceSignedGapMap hp hp1 a) := by
    ext n
    exact not_congr (hzero n)
  rw [he]

/-- Openness makes any collision persist at an actual finite-gap output. -/
theorem exists_symmetric_finiteGap_collision_of_isOpenMap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ho : IsOpenMap (symmetricSourceSignedGapMap hp hp1))
    (a b : RealCoeff p) (hne : a ≠ b)
    (heq : symmetricSourceSignedGapMap hp hp1 a = symmetricSourceSignedGapMap hp hp1 b) :
    ∃ x y : RealCoeff p, x ≠ y ∧
      symmetricRealSourceCoefficients p x ∈ sourceFiniteGapLocus hp hp1 ∧
      symmetricRealSourceCoefficients p y ∈ sourceFiniteGapLocus hp hp1 ∧
      symmetricSourceSignedGapMap hp hp1 x = symmetricSourceSignedGapMap hp hp1 y := by
  let F := symmetricSourceSignedGapMap hp hp1
  obtain ⟨U,V,hU,hV,ha,hb,hUV⟩ := t2_separation hne
  have hmem : F a ∈ F '' U ∩ F '' V := ⟨⟨a,ha,rfl⟩,⟨b,hb,heq.symm⟩⟩
  have ht : Tendsto (fun S : Finset ℤ => RealCoeff.truncate S (F a)) atTop (𝓝 (F a)) := by
    simpa only [RealCoeff.truncatePair,Function.comp_def] using
      (continuous_fst.tendsto (F a,(0 : RealCoeff p))).comp
        (RealCoeff.tendsto_truncatePair hp (F a,0))
  obtain ⟨S,hS⟩ := (ht.eventually (((ho U hU).inter (ho V hV)).mem_nhds hmem)).exists
  obtain ⟨⟨x,hx,hFx⟩,⟨y,hy,hFy⟩⟩ := hS
  have hfinite : (Function.support (RealCoeff.truncate S (F a))).Finite := by
    apply S.finite_toSet.subset
    intro n hn
    by_contra hnot
    simp only [Function.mem_support,RealCoeff.truncate_apply,Finset.mem_coe] at hn hnot
    simp [hnot] at hn
  refine ⟨x,y,?_,?_,?_,hFx.trans hFy.symm⟩
  · intro hxy
    exact Set.disjoint_left.mp hUV hx (hxy.symm ▸ hy)
  · apply (symmetricSource_finiteGap_iff_finite_signedGap_support hp hp1 x).mpr
    rw [hFx]
    exact hfinite
  · apply (symmetricSource_finiteGap_iff_finite_signedGap_support hp hp1 y).mpr
    rw [hFy]
    exact hfinite

/-- Under global openness, signed-gap injectivity reduces to the actual finite-gap locus. -/
theorem symmetricSignedGap_injective_iff_finiteGap_of_isOpenMap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ho : IsOpenMap (symmetricSourceSignedGapMap hp hp1)) :
    Function.Injective (symmetricSourceSignedGapMap hp hp1) ↔
      Set.InjOn (symmetricSourceSignedGapMap hp hp1)
        {a | symmetricRealSourceCoefficients p a ∈ sourceFiniteGapLocus hp hp1} := by
  constructor
  · intro hi
    exact hi.injOn
  · intro hi a b he
    by_contra hne
    obtain ⟨x,y,hxy,hx,hy,hF⟩ := exists_symmetric_finiteGap_collision_of_isOpenMap hp hp1 ho a b hne he
    exact hxy (hi hx hy hF)

end NLS.ZakharovShabat
