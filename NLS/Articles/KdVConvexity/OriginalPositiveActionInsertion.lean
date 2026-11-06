import NLS.Articles.KdVConvexity.OriginalWeightedActionSpace
import NLS.SequenceSpaces.WeightedInsertion
import NLS.SequenceSpaces.PositiveReindex

/-! # Literal insertion of the original positive actions into signed indices

The paper's enumeration of positive actions and the native hierarchy's
positive integer slots carry exactly the same cubic weight. The bounded
linear insertion preserves every raw action and fills nonpositive slots
with zero; it introduces no normalization factor.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def originalPositiveIndexEmbedding : ℤ ↪ ℤ :=
  ⟨positiveIndexInjection actionIndexEquiv,positiveIndexInjection_injective actionIndexEquiv⟩

theorem originalPositiveIndexEmbedding_range (j : ℤ) :
    j∈range originalPositiveIndexEmbedding ↔ 0<j := by
  constructor
  · rintro ⟨k,rfl⟩
    change (0:ℤ)<((actionIndexEquiv k:ℕ):ℤ)
    exact_mod_cast (actionIndexEquiv k).pos
  · intro hj
    refine ⟨actionIndexEquiv.symm ⟨j.toNat,by omega⟩,?_⟩
    have he := actionIndexEquiv.apply_symm_apply (⟨j.toNat,by omega⟩:ℕ+)
    exact (congrArg (fun n : ℕ+ => ((n:ℕ):ℤ)) he).trans (Int.toNat_of_nonneg hj.le)

theorem originalPositiveInsertion_weight (k : ℤ) :
    (Weight.sobolev 3).pullback originalPositiveIndexEmbedding k=originalActionWeight k := by
  change (Weight.sobolev 3) ((actionIndexEquiv k:ℕ):ℤ)=(1+(actionIndexEquiv k:ℝ))^3
  rw [Weight.sobolev_apply,Int.cast_natCast,abs_of_nonneg (by positivity)]
  exact Real.rpow_natCast _ 3

def originalActionInsertionDomain : OriginalActionSpace →L[ℂ]
    WeightedCoeff ((Weight.sobolev 3).pullback originalPositiveIndexEmbedding) 1 :=
  WeightedCoeff.inclusionCLM originalActionWeight ((Weight.sobolev 3).pullback originalPositiveIndexEmbedding)
    (fun k => (originalPositiveInsertion_weight k).le)

def originalPositiveActionInsertion : OriginalActionSpace →L[ℂ] WeightedCoeff (Weight.sobolev 3) 1 :=
  (WeightedCoeff.insertIsometry (p := 1) (Weight.sobolev 3) originalPositiveIndexEmbedding).toContinuousLinearMap.comp
    originalActionInsertionDomain

@[simp] theorem originalPositiveActionInsertion_apply (b : OriginalActionSpace) (n : ℕ+) :
    (originalPositiveActionInsertion b).val (n:ℤ)=b.val (actionIndexEquiv.symm n) := by
  have he : (n:ℤ)=originalPositiveIndexEmbedding (actionIndexEquiv.symm n) := by
    change ((n:ℕ):ℤ)=((actionIndexEquiv (actionIndexEquiv.symm n):ℕ):ℤ)
    rw [Equiv.apply_symm_apply]
  rw [he]
  change (WeightedCoeff.insertIsometry (Weight.sobolev 3) originalPositiveIndexEmbedding _).val
    (originalPositiveIndexEmbedding (actionIndexEquiv.symm n))=_
  exact (WeightedCoeff.insertIsometry_image (Weight.sobolev 3) originalPositiveIndexEmbedding
    (originalActionInsertionDomain b) (actionIndexEquiv.symm n)).trans
      (WeightedCoeff.inclusionCLM_apply _ _ _ b _)

theorem originalPositiveActionInsertion_nonpositive (b : OriginalActionSpace) (j : ℤ) (hj : j≤0) :
    (originalPositiveActionInsertion b).val j=0 := by
  change (WeightedCoeff.insertIsometry (Weight.sobolev 3) originalPositiveIndexEmbedding
    (originalActionInsertionDomain b)).val j=0
  exact WeightedCoeff.insertIsometry_outside _ _ _ j
    (fun h => (not_lt_of_ge hj) ((originalPositiveIndexEmbedding_range j).mp h))

theorem originalPositiveActionInsertion_nonnegative (b : OriginalActionSpace)
    (hb : b∈WeightedCoeff.nonnegativeLocus originalActionWeight 1) :
    originalPositiveActionInsertion b∈WeightedCoeff.nonnegativeLocus (Weight.sobolev 3) 1 := by
  intro j
  by_cases hj : 0<j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have he : (n:ℤ)=j := Int.toNat_of_nonneg hj.le
    rw [←he,originalPositiveActionInsertion_apply]
    exact hb _
  · rw [originalPositiveActionInsertion_nonpositive b j (by omega)]
    simp

/-- Both conventions differentiate in the same raw unit action direction. -/
theorem originalPositiveActionInsertion_single (n : ℕ+) (z : ℂ) :
    originalPositiveActionInsertion (WeightedCoeff.single originalActionWeight (actionIndexEquiv.symm n) z) =
      WeightedCoeff.single (Weight.sobolev 3) (n:ℤ) z := by
  apply Subtype.ext
  funext j
  by_cases hj : 0<j
  · let k : ℕ+ := ⟨j.toNat,by omega⟩
    have he : (k:ℤ)=j := Int.toNat_of_nonneg hj.le
    rw [←he,originalPositiveActionInsertion_apply,WeightedCoeff.single_val,WeightedCoeff.single_val]
    by_cases hkn : k=n
    · subst n
      simp
    · have hk' : actionIndexEquiv.symm k≠actionIndexEquiv.symm n :=
        fun h => hkn (actionIndexEquiv.symm.injective h)
      have hkz : (k:ℤ)≠(n:ℤ) := by
        intro h
        apply hkn
        apply Subtype.ext
        exact Int.ofNat.inj h
      simp only [Pi.single_eq_of_ne hk',Pi.single_eq_of_ne hkz]
  · have hn : (0:ℤ)<(n:ℤ) := by exact_mod_cast n.pos
    have hjn : j≠(n:ℤ) := by omega
    rw [originalPositiveActionInsertion_nonpositive _ j (by omega),WeightedCoeff.single_val,
      Pi.single_eq_of_ne hjn]

end NLS.Articles.KdVConvexity
