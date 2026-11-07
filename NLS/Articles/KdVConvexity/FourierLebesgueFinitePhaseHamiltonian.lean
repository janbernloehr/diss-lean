import NLS.Articles.KdVConvexity.FourierLebesgueFinitePhaseAnalytic
import NLS.Articles.KdVConvexity.FourierLebesguePhaseFrequencyTransport
import NLS.KdV.HillRoughHamiltonianCurveMatching

/-! # Actual finite-support phase-orbit derivatives are physical Hamiltonian vectors

Native norm analyticity supplies the actual time derivative. Its scalar
coordinate derivatives use the original physical frequencies at the
same H1 source. The verified full weak Jacobian injectivity identifies
the whole original Hminus1 direction with the genuine finite action
Gardner vector. There is no derivative or vector-field hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem hasDerivAt_rough_finitePhaseEvolution_hamiltonian
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (hf : (Function.support (D.fourierLebesgueForward s hs p hp h2p q).val.val).Finite)
    (t : ℝ) (a : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (ha : nativeHillSource 1 a.val=fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)
    (S : Finset ℕ+)
    (hS : ∀ n : ℕ+, n∉S → (D.fourierLebesgueForward s hs p hp h2p q).val.val (n : ℤ)=0) :
    HasDerivAt (fun u : ℝ => fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val)
      (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination 1 3 (by norm_num) a S)
        (fourierLebesgueSourceInclusion s hs p hp h2p
          (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)) t := by
  let L : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p →L[ℝ] PeriodOneHminusOne :=
    ((fourierLebesgueSourceInclusion s hs p hp h2p).restrictScalars ℝ).comp
      (physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p).subtypeL
  let U : ℝ → PeriodOneHminusOne := fun u => L (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q)
  have hUa : AnalyticAt ℝ U t := (L.analyticAt _).comp
    (D.analyticAt_fourierLebesguePhaseEvolution_of_finite_support B s hs p hp h2p q hf t)
  let v := deriv U t
  have hU : HasDerivAt U v t := hUa.differentiableAt.hasDerivAt
  have hreal : IsRealPeriodOneHminusOne (U t) :=
    fourierLebesgueSourceInclusion_real s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q)
  have hmean (u : ℝ) : (U u).val 0=0 := by
    change (fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val).val 0=0
    rw [fourierLebesgueSourceInclusion_apply]
    exact (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).property.2
  have hv : v.val 0=0 := by
    let E := (WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0).restrictScalars ℝ
    have hd := E.hasFDerivAt.comp_hasDerivAt t hU
    change HasDerivAt (fun u : ℝ => E (U u)) (E v) t at hd
    have he : (fun u : ℝ => E (U u))=fun _ => (0 : ℂ) := funext hmean
    rw [he] at hd
    exact hd.unique (hasDerivAt_const t 0)
  have hV := D.curve_derivative_eq_finiteActionVector 1 3 (by norm_num) a S U t v hU
    hreal (hmean t) hv
    (fun σ n => D.hasDerivAt_fourierLebesguePhaseEvolution_component_finiteAction B s hs p hp h2p t q a ha S hS σ n)
  rwa [hV] at hU

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
