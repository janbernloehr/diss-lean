import NLS.ZakharovShabat.SourceSection22Phases

/-! # Joint real analyticity of the original scalar phase coordinates

Each scalar coordinate is analytic in time and in the initial rectangular
coordinates throughout the actual open Birkhoff image. The full sequence
trajectory has the compact-time analyticity proved separately.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- The two scalar functions in corrected (4.14) are jointly analytic in real
time and original initial coordinates, for every signed index and finite p > 1. -/
theorem phase_coordinate_joint_analytic (n : ℤ) :
    AnalyticOnNhd ℝ (fun x : ℝ × (RealCoeff p × RealCoeff p) =>
      ((Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency (D.complex.realImageInverse x.2))
        x.1 (Birkhoff.encodeReal x.2)).1 n,
       (Birkhoff.hamiltonianPhaseFlow (A.phaseFrequency (D.complex.realImageInverse x.2))
        x.1 (Birkhoff.encodeReal x.2)).2 n))
      (univ ×ˢ range (sourceRealBirkhoffMap hp hp1 s)) := by
  intro x hx
  have hi := (D.complex.realImageInverse_analytic x.2 hx.2).comp
    (f := fun x : ℝ × (RealCoeff p × RealCoeff p) => x.2) analyticAt_snd
  have hs := ((realTypeSourceSubmodule p).subtypeL.analyticAt _).comp hi
  have hf := ((Q.frequency_analytic n _
    (Q.real_subset (D.complex.realImageInverse x.2).property)).restrictScalars (𝕜 := ℝ)).comp
      (f := fun x : ℝ × (RealCoeff p × RealCoeff p) => (D.complex.realImageInverse x.2).val) hs
  have hw : AnalyticAt ℝ (fun x : ℝ × (RealCoeff p × RealCoeff p) =>
      (2*(Real.pi : ℂ)*n)^2 + A.renormalizedFrequency n (D.complex.realImageInverse x.2).val) x :=
    analyticAt_const.add hf
  have ht : AnalyticAt ℝ (fun x : ℝ × (RealCoeff p × RealCoeff p) => (x.1 : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp analyticAt_fst
  have hc := (Birkhoff.encodeReal.analyticAt x.2).comp
    (f := fun x : ℝ × (RealCoeff p × RealCoeff p) => x.2) analyticAt_snd
  have hz := (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).restrictScalars ℝ).analyticAt _).comp
    (analyticAt_fst.comp hc)
  have hw' := (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).restrictScalars ℝ).analyticAt _).comp
    (analyticAt_snd.comp hc)
  simp only [Birkhoff.hamiltonianPhaseFlow_fst,Birkhoff.hamiltonianPhaseFlow_snd,
    Complex.ofReal_mul,Complex.ofReal_neg,A.phaseFrequency_complex Q.roots.toSourcePsiIsolatingComplexExtension]
  exact (((analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
    ((ht.neg.mul hw).mul analyticAt_const)).mul hz).prod
      (((analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
        ((ht.mul hw).mul analyticAt_const)).mul hw')
end NLS.ZakharovShabat.SourceSection20Data
