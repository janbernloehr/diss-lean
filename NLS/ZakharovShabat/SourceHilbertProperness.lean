import NLS.ZakharovShabat.SourceActionCoefficientContinuity
import NLS.ZakharovShabat.SourceHilbertActionPropernessCriterion

/-! # Properness of the actual Hilbert action and Birkhoff maps

Bounded coefficient continuity of every indexed action is now proved from
the actual spectral contour formula. Together with the action-mass trace
identity and coefficient compactness, this removes the spectral-continuity
premise from both Hilbert properness theorems.
-/
noncomputable section
open Set Filter Topology Complex
namespace NLS.ZakharovShabat

/-- The previously isolated spectral obligation is satisfied by the actual
real Hilbert actions, including all collapsed gaps. -/
theorem sourceHilbertActionsContinuousOnBoundedCoefficients :
    SourceHilbertActionsContinuousOnBoundedCoefficients := by
  intro a b hb ht n
  obtain ⟨M,hM⟩ := hb.exists_norm_le
  have hb' : Bornology.IsBounded (range (fun k => (a k).val)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hM _ ⟨k,rfl⟩
  exact continuous_re.continuousAt.tendsto.comp
    (tendsto_sourceRealAction_of_bounded_coefficientwise (fun k => (a k).val) b.val hb'
      (fun k => (a k).property) b.property ht n)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The full actual Hilbert action sequence map is proper. No separate
spectral continuity or trace-formula assumption is supplied. -/
theorem hilbert_realActionSequence_proper
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    IsProperMap (sourceHilbertRealActionSequence s) :=
  D.hilbert_realActionSequence_proper_of_bounded_coefficient_continuity
    sourceHilbertActionsContinuousOnBoundedCoefficients

/-- The actual real Hilbert Birkhoff map is proper. In particular, inverse
images of compact target sets are compact in the original source norm. -/
theorem hilbert_real_map_proper
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s) :
    IsProperMap (sourceRealBirkhoffMap (by simp) (by norm_num) s) :=
  D.hilbert_real_map_proper_of_bounded_coefficient_continuity
    sourceHilbertActionsContinuousOnBoundedCoefficients

end SourceBirkhoffMapComplexData

/-- A constructed normalized Birkhoff family has both proper Hilbert maps;
no root family or spectral-continuity premise is left to the caller. -/
theorem exists_sourceBirkhoffFamily_hilbert_proper :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s ∧
      IsProperMap (sourceHilbertRealActionSequence s) ∧
      IsProperMap (sourceRealBirkhoffMap (by simp) (by norm_num) s) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨W₀,B,W,s,D,D.hilbert_realActionSequence_proper,D.hilbert_real_map_proper⟩

end NLS.ZakharovShabat
