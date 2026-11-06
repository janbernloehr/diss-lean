import NLS.KdV.HillOriginalFourierDirections
import NLS.KdV.HillFreeCartesianCosineDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Each actual mean-zero sequence coordinate derivative is the original
physical H-minus-one differential, with its literal normalization. -/
theorem hillOriginalMeanZeroDerivativeAtZero_coordinate (k : ℕ)
    (G : PeriodOneHminusOne → ℂ) (hG : AnalyticAt ℂ G 0)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      G (hillOriginalHminusSource p.val) =
        hillSpectralCartesian p.val p.property.1 p.property.2 (k+1) (by omega))
    (h : hillRealMeanZeroSourceSubmodule) :
    hillOriginalMeanZeroDerivativeAtZero h k =
      (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*
        (fderiv ℂ G 0) (hillOriginalRealHminusInclusion h.val) := by
  have hQ0 : (⟨(0 : hillRealSourceSubmodule).val,(0 : hillRealSourceSubmodule).property⟩ : RealPeriodOneHillPotential) =
      (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) := by
    apply Subtype.ext
    rfl
  have hGM0 : ∀ᶠ p : RealPeriodOneHillPotential in
      𝓝 (⟨(0 : hillRealSourceSubmodule).val,(0 : hillRealSourceSubmodule).property⟩ : RealPeriodOneHillPotential),
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian true ⟨k+1,by omega⟩ p := by
    rw [hQ0]
    simpa [hillSignedSpectralCartesian] using hGM
  have hs := hillOriginalRealSpectralMap_coordinate_fderiv (0 : hillRealSourceSubmodule) k G
    (by simpa using hG) hGM0
  have he := congrArg (fun L : hillRealSourceSubmodule →L[ℝ] ℂ => L h.val) hs
  rw [hillOriginalMeanZeroDerivativeAtZero_eq_restriction]
  calc
    _ = (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k)
        ((fderiv ℝ hillOriginalRealSpectralMap 0) h.val) := rfl
    _ = _ := by simpa using he

include h0q h0r in
/-- The ACTUAL original derivative sends each physical cosine direction
to exactly its positive sequence basis vector with factor sqrt(2). -/
theorem hillOriginalMeanZeroDerivativeAtZero_cosine (n : ℕ+) :
    hillOriginalMeanZeroDerivativeAtZero (hillOriginalFourierDirection n 1) =
      lp.single 2 ((n : ℕ)-1) (Real.sqrt 2 : ℂ) := by
  ext k
  let m : ℕ+ := ⟨k+1,by omega⟩
  obtain ⟨Z,W,hZ,hW,_,_,hM,_⟩ := exists_hillFree_cartesian_pair_difference h0q h0r n
  obtain ⟨G,H,hG,_,_,_,hN,_⟩ := exists_hillFree_cartesian_pair_difference h0q h0r m
  have hGM := hN.mono (fun _ hp => hp.1)
  rw [hillOriginalMeanZeroDerivativeAtZero_coordinate h0q h0r k G hG hGM,
    hillOriginalFourierDirection_cosine_hminus,
    hillOriginalCartesian_free_cosine_fderiv h0q h0r n m Z W G hZ hW hG
      (hM.mono (fun _ hp => hp.1)) (hM.mono (fun _ hp => hp.2)) hGM]
  have hn : (n : ℕ) = (m : ℕ) ↔ k = (n : ℕ)-1 := by
    change (n : ℕ) = k+1 ↔ k = (n : ℕ)-1
    have := n.pos
    omega
  simp only [lp.single_apply,Pi.single_apply]
  by_cases he : (n : ℕ) = (m : ℕ)
  · have hnm : n = m := Subtype.ext he
    rw [if_pos he,if_pos (hn.mp he),hnm]
    exact hillActionGapPrefactor_free_base_normalization h0q h0r m m.pos
  · rw [if_neg he,if_neg (mt hn.mpr he),mul_zero]

end NLS.KdV
