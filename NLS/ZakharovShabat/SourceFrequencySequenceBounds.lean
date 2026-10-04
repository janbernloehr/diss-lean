import NLS.ZakharovShabat.SourceFrequencyCorrectionNeighborhood
import NLS.ZakharovShabat.SourceSquaredGapNorm
import NLS.SequenceSpaces.FunctionOrZero

/-! # Actual frequency sequences and their local norm bounds

Adding back the leading squared-gap sequence gives the frequency in
all finite lr with r > 1 and r >= p/2. Every coefficient is verified
against the analytic scalar moment sum, ruling out the total constructor's
zero fallback on the stated neighborhood.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The sequence of actual scalar renormalized frequencies. Membership
results below identify every coordinate on the common source domain. -/
def frequencySequence (A : SourceAbelianMomentAtlas hp hp1 W s)
    (r : ℝ≥0∞) (ψ : CoeffPair p) : Coeff r :=
  Coeff.ofFunctionOrZero r (fun n => A.renormalizedFrequency n ψ)

/-- A correction coefficient sequence and the squared-gap sequence
realize the frequency itself, with its quantitative half-exponent bound. -/
theorem frequencySequence_bound_of_correction [Fact (1 ≤ r)]
    (A : SourceAbelianMomentAtlas hp hp1 W s) (hr : r ≠ ⊤) (hr1 : 1 < r)
    (hpr : ENNReal.ofReal (p.toReal/2) ≤ r) (ψ : CoeffPair p)
    (b : Coeff r) (hb : ∀ n, b n = A.frequencyCorrection ψ n) :
    (∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
      ‖A.frequencySequence r ψ‖ ≤ ‖b‖+‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2/2 := by
  let g := sourcePeriodicSquaredGapCoeff hp hp1 ψ
  let G : Coeff r := ⟨fun n => g n,(lp.memℓp g).of_exponent_ge hpr⟩
  have ht : 0 < ENNReal.ofReal (p.toReal/2) := ENNReal.ofReal_pos.mpr
    (half_pos (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp))
  have hG : ‖G‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ‖^2 :=
    (Coeff.norm_quasiExponentInclusion_le ht (zero_lt_one.trans hr1) hr hpr g).trans
      (norm_sourcePeriodicSquaredGapCoeff_le_sq hp hp1 ψ)
  let f := b-(1/2:ℂ) • G
  have hf (n : ℤ) : f n = A.renormalizedFrequency n ψ := by
    simp only [f,lp.coeFn_sub,Pi.sub_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hb n,
      frequencyCorrection]
    change A.renormalizedFrequency n ψ + (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/2 -
      (1/2:ℂ)*g n = _
    rw [sourcePeriodicSquaredGapCoeff_apply]
    ring
  have hmem : Memℓp (fun n => A.renormalizedFrequency n ψ) r := by
    have hefun : (fun n => f n) = (fun n => A.renormalizedFrequency n ψ) := funext hf
    rw [← hefun]
    exact lp.memℓp f
  have he : A.frequencySequence r ψ = f := by
    ext n
    exact (Coeff.ofFunctionOrZero_apply_of_mem r _ hmem n).trans (hf n).symm
  refine ⟨fun n => Coeff.ofFunctionOrZero_apply_of_mem r _ hmem n,?_⟩
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  norm_num
  linarith

/-- On the same domain as the refined correction, the actual frequency
sequence has locally uniform bounds at every finite target r >= p/2. -/
theorem exists_frequencySequence_neighborhood
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = A.frequencyCorrection ψ n) ∧ ‖b‖ ≤ C) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T,
            (∀ n, A.frequencySequence r ψ n = A.renormalizedFrequency n ψ) ∧
              ‖A.frequencySequence r ψ‖ ≤ C := by
  obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ := A.exists_frequencyCorrection_neighborhood hs hV hrealV
  refine ⟨U,hU,hUc,hreal,hUV,hlocal,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,hcorr⟩ := hlocal φ hφ
  obtain ⟨_,_,G,hG,hφG,R,hR,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  refine ⟨T ∩ G,hT.inter hG,⟨hφT,hφG⟩,fun ψ hψ => hTU hψ.1,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hthird : ENNReal.ofReal (p.toReal/3) ≤ r :=
    (ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])).trans hpr
  obtain ⟨C,hC,hb⟩ := hcorr r hr hr1 hthird
  refine ⟨C+R^2/2,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨b,hbval,hbnorm⟩ := hb ψ hψ.1
  obtain ⟨he,hbound⟩ := A.frequencySequence_bound_of_correction hr hr1 hpr ψ b hbval
  refine ⟨he,hbound.trans ?_⟩
  gcongr
  exact (hgap ψ hψ.2).1

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
