import NLS.ZakharovShabat.SourceActionGapCorrection
import NLS.ZakharovShabat.SourceFrequencyTheorem20_5
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-! # The action-frequency correction in equation (4.12)

Replacing gamma_n^2/2 by twice the actual action preserves the refined
remainder. The corrected map is analytic in every finite lr above one
and at least p/3. This is the source-space input to Theorem 18.1;
analytic descent to action variables is a separate assertion.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
namespace SourceAbelianMomentAtlas

/-- The actual action-frequency correction, before descent to action space. -/
def actionFrequencyCorrection (A : SourceAbelianMomentAtlas hp hp1 W s)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  A.renormalizedFrequency n ψ + 2*sourceComplexAction hp hp1 n ψ

/-- Total realization of the action-frequency correction in a target space. -/
def actionFrequencyCorrectionSequence (A : SourceAbelianMomentAtlas hp hp1 W s)
    (r : ℝ≥0∞) (ψ : CoeffPair p) : Coeff r :=
  Coeff.ofFunctionOrZero r (A.actionFrequencyCorrection ψ)

/-- The exact replacement identity also holds at every closed gap. -/
theorem actionFrequencyCorrection_eq (A : SourceAbelianMomentAtlas hp hp1 W s)
    (ψ : CoeffPair p) (n : ℤ) :
    A.actionFrequencyCorrection ψ n =
      A.frequencyCorrection ψ n + 2*sourceActionGapCorrection hp hp1 ψ n := by
  unfold actionFrequencyCorrection frequencyCorrection sourceActionGapCorrection
  ring

/-- Scalar analyticity and local refined bounds for the action correction
hold on one connected neighborhood, independently of the target exponent. -/
theorem exists_actionFrequencyCorrection_neighborhood
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ n, AnalyticOnNhd ℂ (fun ψ => A.actionFrequencyCorrection ψ n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = A.actionFrequencyCorrection ψ n) ∧ ‖b‖ ≤ C := by
  obtain ⟨B,hB,_,hrealB,hBV,hseq,hfreq⟩ := A.exists_analytic_frequencySequence hs hV hrealV
  obtain ⟨D,hD,_,hrealD,hactA,hact⟩ := exists_sourceActionGapCorrection_neighborhood hp hp1
  let U := connectedComponentIn (B ∩ D) (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := (realTypeSourceSubmodule p).zero_mem
  have hrealBD : realTypeSourceLocus p ⊆ B ∩ D := fun ψ hψ => ⟨hrealB hψ,hrealD hψ⟩
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealBD
  have hUBD : U ⊆ B ∩ D := connectedComponentIn_subset _ _
  have hU : IsOpen U := (hB.inter hD).connectedComponentIn
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨hval,hseqA⟩ := hseq p hp hp1 hhalf
  have hfA (n : ℤ) : AnalyticOnNhd ℂ (A.renormalizedFrequency n) B := by
    intro ψ hψ
    have he := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).analyticAt _).comp (hseqA ψ hψ)
    apply he.congr
    filter_upwards [hB.mem_nhds hψ] with χ hχ
    exact hval χ hχ n
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealBD hzero),hrealU,
    fun ψ hψ => hBV (hUBD hψ).1,?_,?_⟩
  · intro n ψ hψ
    exact (hfA n ψ (hUBD hψ).1).add (analyticAt_const.mul (hactA n ψ (hUBD hψ).2))
  · intro φ hφ
    obtain ⟨T,hT,hφT,_,hfb⟩ := hfreq φ (hUBD hφ).1
    obtain ⟨S,hS,hφS,_,hab⟩ := hact φ (hUBD hφ).2
    refine ⟨(T ∩ S) ∩ U,(hT.inter hS).inter hU,⟨⟨hφT,hφS⟩,hφ⟩,fun _ h => h.2,?_⟩
    intro r hr hr1 hpr
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨Cf,hCf,hf⟩ := hfb r hr hr1 hpr
    obtain ⟨Ca,hCa,ha⟩ := hab r hr hr1 hpr
    refine ⟨Cf+2*Ca,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨f,hf,hfn⟩ := hf ψ hψ.1.1
    obtain ⟨a,ha,han⟩ := ha ψ hψ.1.2
    refine ⟨f+(2:ℂ) • a,?_,?_⟩
    · intro n
      simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hf n,ha n]
      exact (A.actionFrequencyCorrection_eq ψ n).symm
    · apply (norm_add_le _ _).trans
      rw [norm_smul]
      norm_num
      linarith

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
