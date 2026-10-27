import NLS.ZakharovShabat.SymmetricSignedGapGlobalInjectivity

/-! # Exact one-gap variation on the symmetric finite-gap slice

The actual signed-gap map is a homeomorphism over each finite output space.
Varying one output coordinate preserves every other numerical gap length.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- The actual signed-gap map over a fixed finite output support is a
homeomorphism in the inherited Hilbert norm. -/
def symmetricSignedGapFiniteHomeomorph (S : Finset ℤ) :
    {a : RealCoeff 2 | symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
      finiteSignedGapOutputSpace S} ≃ₜ finiteSignedGapOutputSpace S :=
  (Equiv.ofBijective (symmetricSignedGapFiniteRestriction S)
    (bijective_symmetricSignedGapFiniteRestriction S)).toHomeomorphOfContinuousOpen
      (isLocalHomeomorph_symmetricSignedGapFiniteRestriction S).continuous
      (isLocalHomeomorph_symmetricSignedGapFiniteRestriction S).isOpenMap

/-- An exact signed-gap coordinate line has a continuous finite-gap inverse
through the given source, with the same fixed finite spectral support bound. -/
theorem exists_symmetric_signed_gap_curve
    (a : RealCoeff 2) (S : Finset ℤ)
    (ha : symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈ finiteSignedGapOutputSpace S)
    (n : ℤ) (hn : n ∈ S) :
    ∃ c : ℝ → RealCoeff 2, Continuous c ∧ c 0 = a ∧ ∀ t : ℝ,
      symmetricSourceSignedGapMap (by simp) (by norm_num) (c t) =
        symmetricSourceSignedGapMap (by simp) (by norm_num) a + t • lp.single 2 n 1 ∧
      symmetricRealSourceCoefficients 2 (c t) ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  classical
  let H := symmetricSignedGapFiniteHomeomorph S
  let x : {a : RealCoeff 2 | symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈
      finiteSignedGapOutputSpace S} := ⟨a,ha⟩
  let e : finiteSignedGapOutputSpace S := ⟨lp.single 2 n 1,by
    intro k hk
    have hkn : k ≠ n := fun h => hk (h ▸ hn)
    simp [lp.single_apply,hkn]⟩
  let c := fun t : ℝ => (H.symm (H x + t • e)).val
  refine ⟨c,continuous_subtype_val.comp (H.symm.continuous.comp
    (continuous_const.add (continuous_id.smul continuous_const))),?_,fun t => ?_⟩
  · change (H.symm (H x + (0 : ℝ) • e)).val = a
    rw [zero_smul,add_zero,H.symm_apply_apply]
  · have h := congrArg Subtype.val (H.apply_symm_apply (H x + t • e))
    have he : symmetricSourceSignedGapMap (by simp) (by norm_num) (c t) =
        symmetricSourceSignedGapMap (by simp) (by norm_num) a + t • lp.single 2 n 1 := h
    refine ⟨he,symmetricSource_finiteGap_of_signedGap_closed_off_finset (c t) S ?_⟩
    exact (H.symm (H x+t • e)).property

/-- At a collapsed selected gap this curve opens exactly that gap, with
length abs(t), and preserves every other literal periodic gap length. -/
theorem exists_symmetric_exact_gap_opening
    (a : RealCoeff 2) (S : Finset ℤ)
    (ha : symmetricSourceSignedGapMap (by simp) (by norm_num) a ∈ finiteSignedGapOutputSpace S)
    (n : ℤ) (hn : n ∈ S)
    (hzero : symmetricSourceSignedGapMap (by simp) (by norm_num) a n = 0) :
    ∃ c : ℝ → RealCoeff 2, Continuous c ∧ c 0 = a ∧ ∀ t : ℝ,
      symmetricRealSourceCoefficients 2 (c t) ∈ sourceFiniteGapLocus (by simp) (by norm_num) ∧
      (∀ k : ℤ, canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (symmetricSourceCoefficients 2 (c t))) (periodOnePotential_mem _) k =
        if k = n then ((|t| : ℝ) : ℂ) else canonicalPeriodicGap (by simp) (by norm_num)
          (periodOnePotential (symmetricSourceCoefficients 2 a)) (periodOnePotential_mem _) k) := by
  obtain ⟨c,hc,hc0,he⟩ := exists_symmetric_signed_gap_curve a S ha n hn
  refine ⟨c,hc,hc0,fun t => ⟨(he t).2,fun k => ?_⟩⟩
  rw [periodicGap_symmetricSource_eq_abs_signedGap,(he t).1]
  change ((|symmetricSourceSignedGapMap (by simp) (by norm_num) a k +
    t * (lp.single 2 n 1 : RealCoeff 2) k| : ℝ) : ℂ) = _
  by_cases hkn : k = n
  · subst k
    simp only [hzero,lp.single_apply,Pi.single_eq_same,mul_one,zero_add,ite_true]
  · rw [if_neg hkn,periodicGap_symmetricSource_eq_abs_signedGap]
    simp only [lp.single_apply,Pi.single_eq_of_ne hkn,mul_zero,add_zero]

end NLS.ZakharovShabat
