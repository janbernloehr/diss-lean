import NLS.ZakharovShabat.SourceFiniteGapMomentumNormalization
import NLS.ZakharovShabat.SourceSobolevHamiltonianDifferential

/-! # The physical angle–momentum identity on real H¹ and complex germs

H¹ finite-gap density preserves the selected open gap and extends the
actual bracket identity to every real H¹ source. Analytic uniqueness
then gives a complex germ at each such source, for each selected index.
No common domain for countably many indices or full-domain continuation
is asserted here.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- H¹ finite-gap density preserving the selected open gap gives the normalization on all real H¹. -/
theorem realSobolev_momentum_bracket_normalized
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n u a.val = 2*(Real.pi : ℂ)*n := by
  let q : realTypeSobolevSourceLocus → realTypeSourceSubmodule 2 :=
    fun b => ⟨sobolevSourceInclusion b.val,b.property⟩
  have hq : Continuous q := (sobolevSourceInclusion.continuous.comp continuous_subtype_val).subtype_mk _
  let G := q ⁻¹' sourceOpenGapRealLocus (by simp) (by norm_num) n
  have hG : IsOpen G := (isOpen_sourceOpenGapRealLocus (by simp) (by norm_num) n).preimage hq
  apply eq_of_continuousOn_of_sourceSobolevFiniteGap hG (H := fun b => sourceSobolevThetaMomentumBracket n u b.val)
    (c := 2*(Real.pi : ℂ)*n) ?_ ?_ a hn
  · intro b hb
    have h := (E.analyticOnNhd_sobolevThetaMomentumBracket n b.val ⟨E.real_subset b.property,hb⟩).continuousAt
    exact (h.comp continuous_subtype_val.continuousAt).continuousWithinAt
  · intro b hb hbf
    have he := D.finiteGap_momentum_bracket_normalized E F A (q b) hbf n hb
    simpa only [q,sourceFiniteGapSobolevPair_sobolevSource] using he
end NLS.ZakharovShabat.SourceBirkhoffMapComplexData

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V X U Wa : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Real-form analytic uniqueness gives a constant complex germ at each real open-gap H¹ source. -/
theorem eventually_sobolev_momentum_bracket_normalized
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (F : SourceFullAbelianDifferentialData (by simp) (by norm_num) X U)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa u)
    (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n u =ᶠ[𝓝 a.val] (fun _ => 2*(Real.pi : ℂ)*n) := by
  classical
  let gap : (ScalarDomain 2 × ScalarDomain 2) → ℂ := fun b => canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion b)) (periodOnePotential_mem _) n
  have hgap : ContinuousAt gap a.val := by
    have hl := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      (by simp) (by norm_num) (sobolevSourceInclusion a.val) a.property n
    have hr := continuousAt_canonicalPeriodicRight_periodOne_of_realType
      (by simp) (by norm_num) (sobolevSourceInclusion a.val) a.property n
    exact (hr.sub hl).comp sobolevSourceInclusion.continuous.continuousAt
  have hopen : ∀ᶠ b in 𝓝 a.val, gap b ≠ 0 := hgap.eventually (isOpen_compl_singleton.mem_nhds hn)
  let c : ℂ := 2*(Real.pi : ℂ)*n
  let f : (ScalarDomain 2 × ScalarDomain 2) → ℂ :=
    fun b => if gap b ≠ 0 then sourceSobolevThetaMomentumBracket n u b else c
  have he : sourceSobolevThetaMomentumBracket n u =ᶠ[𝓝 a.val] f := by
    filter_upwards [hopen] with b hb
    simp only [f,if_pos hb]
  have hf : AnalyticAt ℂ f a.val :=
    (E.analyticOnNhd_sobolevThetaMomentumBracket n a.val ⟨E.real_subset a.property,hn⟩).congr he
  have hreal (b : realTypeSobolevSourceLocus) : f b.val = c := by
    dsimp only [f]
    split_ifs with hb
    · exact D.realSobolev_momentum_bracket_normalized E F A b n hb
    · rfl
  exact he.trans (eventuallyEq_sobolev_of_analyticAt_of_real_agreement a f (fun _ => c)
    hf analyticAt_const hreal)
end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
