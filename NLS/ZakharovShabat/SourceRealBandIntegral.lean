import NLS.ZakharovShabat.SourceRealBandArcsin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The adjacent-band improper quotient integral is `-i*pi`

Every compact subinterval of a real spectral band admits the actual
arcsine evaluation. Letting its two endpoints approach the periodic
endpoints independently gives exactly `-i*pi`, including adjacent
collapsed gaps and every signed index.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual quotient integral along a real interval. -/
def sourceRealBandIntegral (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (u v : ℝ) : ℂ :=
  ∫ x in u..v, deriv (canonicalDiscriminant hp (periodOnePotential φ)) (x : ℂ) /
    sourceCanonicalRoot hp hp1 φ (x : ℂ)

/-- No integrability assumption is needed inside a band: continuity
supplies it, and the arcsine primitive evaluates the actual integral. -/
theorem sourceRealBandIntegral_eq_sub
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (u v : ℝ)
    (hu : u ∈ sourceRealBand hp hp1 φ n) (hv : v ∈ sourceRealBand hp hp1 φ n) :
    sourceRealBandIntegral hp hp1 φ u v =
      sourceRealBandArcsinPrimitive hp φ n v-sourceRealBandArcsinPrimitive hp φ n u := by
  have hsub : uIcc u v ⊆ sourceRealBand hp hp1 φ n := ordConnected_Ioo.uIcc_subset hu hv
  have hcont : ContinuousOn (fun x : ℝ =>
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) (x : ℂ) /
        sourceCanonicalRoot hp hp1 φ (x : ℂ)) (uIcc u v) := by
    intro x hx
    exact ((sourceCriticalRootRatio_analyticOnNhd hp hp1 φ (x : ℂ)
      (sourceRealBand_subset_rootDomain hp hp1 φ hφ n x (hsub hx))).continuousAt.comp
        continuous_ofReal.continuousAt).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_sourceRealBandArcsinPrimitive hp hp1 φ hφ n x (hsub hx))
    hcont.intervalIntegrable

/-- Independent approaches to the two band endpoints give the exact
improper integral in the proof of Lemma 19.1(ii). -/
theorem sourceRealBandIntegral_tendsto_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    Tendsto (fun uv : ℝ × ℝ => sourceRealBandIntegral hp hp1 φ uv.1 uv.2)
      (𝓝[sourceRealBand hp hp1 φ n ×ˢ sourceRealBand hp hp1 φ n]
        ((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re,
          (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re))
      (𝓝 (-I*(Real.pi : ℂ))) := by
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
  let P := sourceRealBandArcsinPrimitive hp φ n
  have hP : Continuous P := continuous_sourceRealBandArcsinPrimitive hp hp1 φ n
  have hc : Continuous (fun uv : ℝ × ℝ => P uv.2-P uv.1) :=
    (hP.comp (continuous_snd : Continuous (Prod.snd : ℝ × ℝ → ℝ))).sub
      (hP.comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ)))
  have hlim : Tendsto (fun uv : ℝ × ℝ => P uv.2-P uv.1)
      (𝓝[sourceRealBand hp hp1 φ n ×ˢ sourceRealBand hp hp1 φ n] (a,b)) (𝓝 (P b-P a)) :=
    (hc.continuousAt (x := (a,b))).tendsto.mono_left nhdsWithin_le_nhds
  have he : P b-P a = -I*(Real.pi : ℂ) := by
    rw [show P b = -I*(Real.pi : ℂ)/2 from sourceRealBandArcsinPrimitive_right hp hp1 φ hφ n,
      show P a = I*(Real.pi : ℂ)/2 from sourceRealBandArcsinPrimitive_left hp hp1 φ hφ n]
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with uv huv
  exact (sourceRealBandIntegral_eq_sub hp hp1 φ hφ n uv.1 uv.2 huv.1 huv.2).symm

/-- An explicit positive cutoff approaches both endpoints from inside
the nonempty band and realizes the same improper integral. -/
theorem sourceRealBandIntegral_symmetric_cutoff_tendsto
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
    Tendsto (fun ε : ℝ => sourceRealBandIntegral hp hp1 φ (a+ε) (b-ε))
      (𝓝[>] 0) (𝓝 (-I*(Real.pi : ℂ))) := by
  dsimp only
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let b := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re
  have hab : a < b := canonicalPeriodicRight_re_lt_next_left hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have ht : Tendsto (fun ε : ℝ => (a+ε,b-ε)) (𝓝[>] 0)
      (𝓝[sourceRealBand hp hp1 φ n ×ˢ sourceRealBand hp hp1 φ n] (a,b)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun ε : ℝ => (a+ε,b-ε)) :=
        (continuous_const.add continuous_id).prodMk (continuous_const.sub continuous_id)
      simpa only [add_zero,sub_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr hab)] with ε hε
      change (a < a+ε ∧ a+ε < b) ∧ (a < b-ε ∧ b-ε < b)
      constructor <;> constructor <;> linarith [hε.1,hε.2]
  exact (sourceRealBandIntegral_tendsto_endpoints hp hp1 φ hφ n).comp ht

end NLS.ZakharovShabat
