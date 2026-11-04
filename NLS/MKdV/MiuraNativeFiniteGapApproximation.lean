import NLS.MKdV.MiuraFiniteGapPhaseRotation
import NLS.SequenceSpaces.RealCoeffTruncation

/-! # Norm approximation by actual native finite-gap profiles

Truncating the original normalized Cartesian coordinates and decoding
through the global native homeomorphism produces actual real Sobolev
profiles with a finite closed-gap complement. The approximants converge
in the original Hˢ norm. Complete action flows are continuous in their
initial native profile.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV
open scoped ENNReal
namespace NLS.MKdV

def miuraNativeFiniteGapApproximation (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (S : Finset ℤ) : MiuraRealSobolevSource s :=
  (miuraNativeNormalizedHomeomorph s hs).symm (miuraRealCartesianDecoder
    (RealCoeff.truncatePair S (WeightedCoeff.positiveCartesianRealParameters
      (Weight.sobolev (1/2)) 2 (miuraNativeNormalizedHomeomorph s hs a).val)))

theorem tendsto_miuraNativeFiniteGapApproximation (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    Tendsto (miuraNativeFiniteGapApproximation s hs a) atTop (𝓝 a) := by
  have ht := ((miuraNativeNormalizedHomeomorph s hs).symm.continuous.comp miuraRealCartesianDecoder.continuous).tendsto
    (WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2 (miuraNativeNormalizedHomeomorph s hs a).val)
  have h := ht.comp (RealCoeff.tendsto_truncatePair (by simp : (2:ℝ≥0∞) ≠ ⊤) _)
  change Tendsto (miuraNativeFiniteGapApproximation s hs a) atTop
    (𝓝 ((miuraNativeNormalizedHomeomorph s hs).symm (miuraRealCartesianDecoder
      (WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2
        (miuraNativeNormalizedHomeomorph s hs a).val)))) at h
  simpa only [miuraRealCartesianDecoder_parameters,Homeomorph.symm_apply_apply] using h

theorem miuraNativeFiniteGapApproximation_closedComplement
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (S : Finset ℤ) :
    miuraNativeFiniteGapApproximation s hs a S ∈
      miuraNativeClosedComplement s hs (S.image (fun m : ℤ => m.toNat-1)) := by
  classical
  intro k hk
  have hkS : ((k+1:ℕ):ℤ) ∉ S := by
    intro hm
    apply hk
    exact Finset.mem_image.mpr ⟨_,hm,by simp only [Int.toNat_natCast,Nat.add_sub_cancel]⟩
  apply (miuraNativeHill_halfLength_zero_iff_angular_zero s hs _ (k+1) (by omega)).mpr
  have he : miuraPositiveCartesianEval (k+1:ℕ)
      (miuraNativeNormalizedHomeomorph s hs (miuraNativeFiniteGapApproximation s hs a S)).val = 0 := by
    rw [miuraNativeFiniteGapApproximation,Homeomorph.apply_symm_apply]
    change WeightedCoeff.positiveCartesianEval (Weight.sobolev (1/2)) 2 (k+1:ℕ)
      (WeightedCoeff.positiveCartesianRealDecoder (Weight.sobolev (1/2)) 2 _) = 0
    rw [WeightedCoeff.positiveCartesianRealDecoder_eval,if_pos (by omega : (0:ℤ) < (k+1:ℕ))]
    simp only [RealCoeff.truncatePair,RealCoeff.truncate_apply,if_neg hkS,Complex.ofReal_zero,zero_div]
    rfl
  rw [miuraNativeNormalizedHomeomorph_apply] at he
  change (miuraPositiveCartesianEval (k+1:ℕ) (miuraSobolevNormalizedCartesianMap s
      (miuraNativeFiniteGapApproximation s hs a S).val)).1-
    I*(miuraPositiveCartesianEval (k+1:ℕ) (miuraSobolevNormalizedCartesianMap s
      (miuraNativeFiniteGapApproximation s hs a S).val)).2 = 0
  rw [he]
  simp only [Prod.fst_zero,Prod.snd_zero,mul_zero,sub_zero]

theorem continuous_miuraNativeRealActionFlow_initial
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    Continuous (fun a : MiuraRealSobolevSource s => miuraNativeRealActionFlow s a j t) := by
  have hc : Continuous (fun a : MiuraRealSobolevSource s =>
      (miuraNativeNormalizedHomeomorph s hs (miuraNativeRealActionFlow s a j t)).val) :=
    ((miuraCartesianRotation j t).continuous.comp
      (continuous_subtype_val.comp (miuraNativeNormalizedHomeomorph s hs).continuous)).congr
        (fun a => (miuraNativeNormalizedHomeomorph_actionFlow s hs a j hj t).symm)
  have hH : Continuous (fun a : MiuraRealSobolevSource s =>
      miuraNativeNormalizedHomeomorph s hs (miuraNativeRealActionFlow s a j t)) :=
    hc.subtype_mk (fun a => (miuraNativeNormalizedHomeomorph s hs (miuraNativeRealActionFlow s a j t)).property)
  exact ((miuraNativeNormalizedHomeomorph s hs).symm.continuous.comp hH).congr
    (fun a => (miuraNativeNormalizedHomeomorph s hs).symm_apply_apply (miuraNativeRealActionFlow s a j t))

end NLS.MKdV
