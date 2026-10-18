import NLS.ZakharovShabat.SourceBirkhoffComplexSpectralTerminal

/-! # Stronger-target analyticity of the complex angular error

Both actual signed terminal errors are analytic in the h2 norm, represented by their exact weighted coefficients. The decoder uses 1+|2n|, not the physical piSobolev norm. The two sharp Fourier spectral errors and full one-smoothing remain open.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Actual signed terminal error in the stronger h2 weight; local membership is proved below. -/
def normalizedSobolevBirkhoffSpectralTerminalError
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (sign : ℂ) (ψ : CoeffPair 2) : Coeff 2 :=
  Coeff.ofFunctionOrZero 2 (fun n => ((Weight.sobolev 2 n):ℂ)*
    (sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s sign
        (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)-
      sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n sign
        (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)))

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

set_option maxHeartbeats 800000 in
/-- Both signed terminal errors are analytic in their stronger h2 norm on one complex first-order Sobolev neighborhood. -/
theorem exists_local_normalizedSobolevBirkhoffSpectralTerminal_analytic (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ sign : ℝ, sign=1 ∨ sign= -1 →
        AnalyticOnNhd ℂ (normalizedSobolevBirkhoffSpectralTerminalError s (sign:ℂ)) U ∧
        ∀ ψ ∈ U, ‖normalizedSobolevBirkhoffSpectralTerminalError s (sign:ℂ) ψ‖ ≤ M ∧
          ∀ n, normalizedSobolevBirkhoffSpectralTerminalError s (sign:ℂ) ψ n =
            ((Weight.sobolev 2 n):ℂ)*(sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ)
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)-
              sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (sign:ℂ)
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)) := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let L := normalizedWeightedSourceCLM (p := 2) w
  let φu : realTypeSourceSubmodule 2 := ⟨L φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Vb,hVb,hφb,M,hM,hbound⟩ := D.exists_local_normalizedSobolevBirkhoffSpectralTerminal_bound φ
  obtain ⟨Va,hVa,hφa,A,hA,ha⟩ := D.exists_local_normalizedWeightedEta_analytic w φ
  obtain ⟨Vr,hVr,hφr,hr,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic
    (by simp) (by norm_num) φu.val φu.property
  obtain ⟨Ve,hVe,hφe,_,he⟩ := D.exists_local_etaRemainder_allIndices_analytic φu
  let U := Vb ∩ (Va ∩ L ⁻¹' (Vr ∩ (Ve ∩ W)))
  have hU : IsOpen U := hVb.inter (hVa.inter ((hVr.inter (hVe.inter D.source_open)).preimage L.continuous))
  have hφU : φ.val ∈ U := ⟨hφb,hφa,hφr,hφe,D.real_subset φu.property⟩
  refine ⟨U,hU,hφU,M,hM,?_⟩
  intro sign hsign
  have hs : (sign:ℂ)=1 ∨ (sign:ℂ)= -1 := by rcases hsign with rfl | rfl <;> simp
  let F := normalizedSobolevBirkhoffSpectralTerminalError s (sign:ℂ)
  have hdata (ψ : CoeffPair 2) (hψ : ψ ∈ U) : ‖F ψ‖ ≤ M ∧ ∀ n,
      F ψ n = ((Weight.sobolev 2 n):ℂ)*(sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ) (L ψ)-
        sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (sign:ℂ) (L ψ)) := by
    obtain ⟨z,hz,hnz⟩ := hbound ψ hψ.1 sign hsign
    have hmem := lp.memℓp (WeightedCoeff.weightEquiv (Weight.sobolev 2) 2 z)
    change Memℓp (fun n => ((Weight.sobolev 2 n):ℂ)*z.val n) 2 at hmem
    simp only [hz] at hmem
    have hF (n : ℤ) : F ψ n = ((Weight.sobolev 2 n):ℂ)*z.val n := by
      rw [hz]
      exact Coeff.ofFunctionOrZero_apply_of_mem 2 _ hmem n
    have hFeq : F ψ = WeightedCoeff.weightEquiv (Weight.sobolev 2) 2 z := by
      ext n
      exact hF n
    refine ⟨?_,fun n => (hF n).trans (by rw [hz]; rfl)⟩
    rw [hFeq]
    exact hnz
  refine ⟨?_,hdata⟩
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise F hU _ M (fun ψ hψ => (hdata ψ hψ).1)
  intro n ψ hψ
  let G := normalizedWeightedEtaSequence (by simp) (by norm_num) s w (sign:ℂ)
  have hG : AnalyticAt ℂ (fun χ => G χ n) ψ :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp ((ha (sign:ℂ) hs).1 ψ hψ.2.1)
  have hwne : (w (2*n):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (w.positive _))
  have hη : AnalyticAt ℂ (fun χ : CoeffPair 2 => sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) (L χ)) ψ := by
    apply (hG.div_const (c := (w (2*n):ℂ))).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    change G χ n/(w (2*n):ℂ) = _
    rw [((ha (sign:ℂ) hs).2 χ hχ.2.1).2 n]
    exact mul_div_cancel_left₀ _ hwne
  have hroot : AnalyticAt ℂ (fun χ : CoeffPair 2 => sourceNormalizedActionRoot (by simp) (by norm_num) n (L χ)) ψ :=
    (hr n (L ψ) hψ.2.2.1).comp (L.analyticAt ψ)
  have hβ : AnalyticAt ℂ (fun χ : CoeffPair 2 => sourceAngularBetaCorrection (by simp) (by norm_num) n s (L χ)) ψ :=
    (D.angular.beta_series.analytic_correction n (L ψ) (D.source_subset hψ.2.2.2.2)).comp (L.analyticAt ψ)
  have hrem : AnalyticAt ℂ (fun χ : CoeffPair 2 => sourceAngularEtaRemainder (by simp) (by norm_num) n s (L χ)) ψ :=
    (he n (L ψ) hψ.2.2.2.1).comp (L.analyticAt ψ)
  have hexpβ : AnalyticAt ℂ (fun χ : CoeffPair 2 => exp ((sign:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s (L χ))) ψ :=
    (analyticAt_const.mul hβ).cexp'
  have hexpη : AnalyticAt ℂ (fun χ : CoeffPair 2 => exp (-(sign:ℂ)*I*sourceAngularEtaRemainder (by simp) (by norm_num) n s (L χ))) ψ :=
    (analyticAt_const.mul hrem).cexp'
  have han : AnalyticAt ℂ (fun χ : CoeffPair 2 => ((Weight.sobolev 2 n):ℂ)*
      ((sourceNormalizedActionRoot (by simp) (by norm_num) n (L χ)*
        exp ((sign:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s (L χ))-
        exp (-(sign:ℂ)*I*sourceAngularEtaRemainder (by simp) (by norm_num) n s (L χ)))*
        sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s (sign:ℂ) (L χ))) ψ :=
    analyticAt_const.mul (((hroot.mul hexpβ).sub hexpη).mul hη)
  apply han.congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  rw [(hdata χ hχ).2 n,sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase (by simp) (by norm_num) n s]
  simp only [sourceBirkhoffWeightedCoordinate]
  ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat

/-- Actual signed terminal error as an h2-valued map; its coefficients are identified on the local domain below. -/
def normalizedSobolevBirkhoffSpectralTerminalH2
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (sign : ℂ) (ψ : CoeffPair 2) :
    WeightedCoeff (Weight.sobolev 2) 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm
    (normalizedSobolevBirkhoffSpectralTerminalError s sign ψ)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- Stronger-target analyticity expressed directly in h2, with the actual unweighted error as every coefficient. -/
theorem exists_local_normalizedSobolevBirkhoffSpectralTerminalH2_analytic (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ sign : ℝ, sign=1 ∨ sign= -1 →
        AnalyticOnNhd ℂ (normalizedSobolevBirkhoffSpectralTerminalH2 s (sign:ℂ)) U ∧
        ∀ ψ ∈ U, ‖normalizedSobolevBirkhoffSpectralTerminalH2 s (sign:ℂ) ψ‖ ≤ M ∧
          ∀ n, (normalizedSobolevBirkhoffSpectralTerminalH2 s (sign:ℂ) ψ).val n =
            sourceBirkhoffWeightedCoordinate (by simp) (by norm_num) n s (sign:ℂ)
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)-
              sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) n (sign:ℂ)
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ) := by
  obtain ⟨U,hU,hφ,M,hM,h⟩ := D.exists_local_normalizedSobolevBirkhoffSpectralTerminal_analytic φ
  refine ⟨U,hU,hφ,M,hM,?_⟩
  intro sign hs
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact ((WeightedCoeff.weightIsometry (Weight.sobolev 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      ((h sign hs).1 ψ hψ)
  · intro ψ hψ
    refine ⟨?_,?_⟩
    · simpa only [normalizedSobolevBirkhoffSpectralTerminalH2,LinearIsometryEquiv.norm_map] using
        ((h sign hs).2 ψ hψ).1
    · intro n
      change normalizedSobolevBirkhoffSpectralTerminalError s (sign:ℂ) ψ n/((Weight.sobolev 2 n):ℂ) = _
      rw [((h sign hs).2 ψ hψ).2 n]
      exact mul_div_cancel_left₀ _ ((Weight.sobolev 2).complex_ne_zero n)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
