import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.ZakharovShabat.SourceBirkhoffHmComplexSpectralTerminal
import NLS.ZakharovShabat.SourceBirkhoffComplexSpectralTerminalAnalytic

/-! # Higher-order angular analyticity in the stronger target

For every integer m >= 1, the actual signed angular-error map is analytic with values in h^(m+1) on a complex neighborhood of each real Hm source. Its raw coefficients are the original errors.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The actual signed angular error realized in the one-order-stronger sequence space. -/
def higherSobolevBirkhoffSpectralTerminalError (m : ℕ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (sign : ℂ) (b : SobolevSource m) :
    WeightedCoeff (Weight.sobolev ((m:ℝ)+1)) 2 :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev ((m:ℝ)+1)) 2 (fun n =>
    sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s sign (higherSobolevSourceInclusion m b)-
      sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n sign (higherSobolevSourceInclusion m b))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The original angular error is locally bounded and analytic from every complex Hm source neighborhood into h^(m+1). -/
theorem exists_local_higherSobolevBirkhoffSpectralTerminal_analytic (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧ a.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ sign : ℝ, sign=1 ∨ sign= -1 →
        AnalyticOnNhd ℂ (higherSobolevBirkhoffSpectralTerminalError m s (sign:ℂ)) U ∧
        ∀ b ∈ U, ‖higherSobolevBirkhoffSpectralTerminalError m s (sign:ℂ) b‖ ≤ M ∧
          ∀ n, (higherSobolevBirkhoffSpectralTerminalError m s (sign:ℂ) b).val n =
            sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ) (higherSobolevSourceInclusion m b)-
              sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (sign:ℂ) (higherSobolevSourceInclusion m b) := by
  let J := higherSobolevFirstNormalizedCoordinates m hm
  let φ : realTypeSourceLocus 2 := ⟨J a.val,higherSobolevFirstNormalizedCoordinates_realType m hm a⟩
  obtain ⟨Vb,hVb,hφb,M,hM,hbound⟩ := D.exists_local_higherSobolevBirkhoffSpectralTerminal_bound m hm a
  obtain ⟨Va,hVa,hφa,A,hA,ha⟩ := D.exists_local_normalizedSobolevBirkhoffSpectralTerminalH2_analytic φ
  let U := Vb ∩ J ⁻¹' Va
  have hU : IsOpen U := hVb.inter (hVa.preimage J.continuous)
  refine ⟨U,hU,⟨hφb,hφa⟩,M,hM,?_⟩
  intro sign hs
  apply WeightedCoeff.analytic_realization_of_bound (Weight.sobolev ((m:ℝ)+1)) _ hU _ M
    (fun b hb => hbound b hb.1 sign hs)
  intro n b hb
  let e := WeightedCoeff.evalCLM (Weight.sobolev 2) 2 n
  have hscalar : AnalyticAt ℂ (fun c : SobolevSource m => e (normalizedSobolevBirkhoffSpectralTerminalH2 s (sign:ℂ) (J c))) b :=
    (e.analyticAt _).comp (((ha sign hs).1 (J b) hb.2).comp (J.analyticAt b))
  apply hscalar.congr
  filter_upwards [hU.mem_nhds hb] with c hc
  change (normalizedSobolevBirkhoffSpectralTerminalH2 s (sign:ℂ) (J c)).val n = _
  rw [((ha sign hs).2 (J c) hc.2).2 n,normalizedWeightedSource_higherSobolevFirstNormalizedCoordinates]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
