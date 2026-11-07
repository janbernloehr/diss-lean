import NLS.SequenceSpaces.SignedSobolevWienerWeakStar
import NLS.SequenceSpaces.FourierRealZeroSubmodule

/-! The actual physical real, zero-mode signed sequence is tested against
its opposite-order physical real, zero-mode Wiener predual. The scalar
pairing is the real part of the absolutely convergent opposite-index sum. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- The actual real Wiener functional, with the original physical real forms. -/
def physicalSignedWienerFunctional (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) ⊤) :
    fourierRealZeroSubmodule (Weight.signedSobolev (-s)) 1 →L[ℝ] ℝ :=
  Complex.reCLM.comp (((signedSobolevBilinearPairing s a.val.val).restrictScalars ℝ).comp
    (((zeroModeSubmodule (Weight.signedSobolev (-s)) 1).subtypeL.restrictScalars ℝ).comp
      (fourierRealZeroSubmodule (Weight.signedSobolev (-s)) 1).subtypeL))

def physicalSignedWeakStar (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) ⊤) :
    WeakDual ℝ (fourierRealZeroSubmodule (Weight.signedSobolev (-s)) 1) :=
  StrongDual.toWeakDual (physicalSignedWienerFunctional s a)

theorem physicalSignedWeakStar_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) ⊤)
    (b : fourierRealZeroSubmodule (Weight.signedSobolev (-s)) 1) :
    physicalSignedWeakStar s a b = (∑' n : ℤ, a.val.val.val n*b.val.val.val (-n)).re := by
  change (signedSobolevBilinearPairing s a.val.val b.val.val).re = _
  rw [signedSobolevBilinearPairing_apply]

/-- Arbitrary bounded physical families converge in the actual physical real
Wiener weak-star topology when all their literal coefficients converge. -/
theorem tendsto_physicalSignedWeakStar_of_bounded_coefficients
    (s : ℝ) {X : Type*} {l : Filter X}
    (x : X → fourierRealZeroSubmodule (Weight.signedSobolev s) ⊤)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => (x k).val.val.val n) l (𝓝 (a.val.val.val n))) :
    Tendsto (fun k => physicalSignedWeakStar s (x k)) l (𝓝 (physicalSignedWeakStar s a)) := by
  have hb' : Bornology.IsBounded (range (fun k => (x k).val.val)) := by
    obtain ⟨R,hR⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hR _ (mem_range_self k)
  have ht := tendsto_signedSobolevWeakStar_of_bounded_coefficients s
    (fun k => (x k).val.val) a.val.val hb' hc
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro b
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp ht b.val.val)

end NLS.WeightedCoeff
