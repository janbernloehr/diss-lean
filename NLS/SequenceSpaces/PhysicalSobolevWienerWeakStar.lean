import NLS.SequenceSpaces.WeightedWienerWeakStar
import NLS.SequenceSpaces.FourierRealZeroSubmodule

/-! The actual physical real, zero-mode Sobolev sequence is tested against
its opposite-order physical real, zero-mode Wiener predual using the literal1+abs(n) bracket. The scalar
pairing is the real part of the absolutely convergent opposite-index sum. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- The actual real Wiener functional, with the original physical real forms. -/
def physicalSobolevWienerFunctional (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤) :
    fourierRealZeroSubmodule (Weight.sobolev (-s)) 1 →L[ℝ] ℝ :=
  Complex.reCLM.comp (((sobolevBilinearPairing s a.val.val).restrictScalars ℝ).comp
    (((zeroModeSubmodule (Weight.sobolev (-s)) 1).subtypeL.restrictScalars ℝ).comp
      (fourierRealZeroSubmodule (Weight.sobolev (-s)) 1).subtypeL))

def physicalSobolevWeakStar (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤) :
    WeakDual ℝ (fourierRealZeroSubmodule (Weight.sobolev (-s)) 1) :=
  StrongDual.toWeakDual (physicalSobolevWienerFunctional s a)

theorem physicalSobolevWeakStar_apply (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤)
    (b : fourierRealZeroSubmodule (Weight.sobolev (-s)) 1) :
    physicalSobolevWeakStar s a b = (∑' n : ℤ, a.val.val.val n*b.val.val.val (-n)).re := by
  change (sobolevBilinearPairing s a.val.val b.val.val).re = _
  rw [sobolevBilinearPairing_apply]

/-- Arbitrary bounded physical families converge in the actual physical real
Wiener weak-star topology when all their literal coefficients converge. -/
theorem tendsto_physicalSobolevWeakStar_of_bounded_coefficients
    (s : ℝ) {X : Type*} {l : Filter X}
    (x : X → fourierRealZeroSubmodule (Weight.sobolev s) ⊤)
    (a : fourierRealZeroSubmodule (Weight.sobolev s) ⊤)
    (hb : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => (x k).val.val.val n) l (𝓝 (a.val.val.val n))) :
    Tendsto (fun k => physicalSobolevWeakStar s (x k)) l (𝓝 (physicalSobolevWeakStar s a)) := by
  have hb' : Bornology.IsBounded (range (fun k => (x k).val.val)) := by
    obtain ⟨R,hR⟩ := hb.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨R,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hR _ (mem_range_self k)
  have ht := tendsto_sobolevWeakStar_of_bounded_coefficients s
    (fun k => (x k).val.val) a.val.val hb' hc
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro b
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_iff_forall_eval_tendsto_topDualPairing.mp ht b.val.val)

end NLS.WeightedCoeff
