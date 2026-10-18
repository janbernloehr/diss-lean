import NLS.ZakharovShabat.SourceNormalizedRootComplexLower
import NLS.ZakharovShabat.SourceEtaInverseNormalization
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexBound
import NLS.ZakharovShabat.SourceAngularBetaCorrectionBound
import NLS.SequenceSpaces.TwoSequenceBound

/-! # Native complex weighted eta bounds

The inverse normalization and the native weighted Birkhoff bound give actual weighted eta membership and locally uniform norms on a common complex neighborhood.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- Actual eta coordinates preserve every spectral weight on a complex neighborhood of each weighted real source. -/
theorem exists_local_normalizedWeightedEta_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∀ sign : ℂ, sign = 1 ∨ sign = -1 →
        Memℓp (fun n => (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign (normalizedWeightedSource w ψ)) p ∧
        ‖Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign
          (normalizedWeightedSource w ψ))‖ ≤ M := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ux,hUx,hφx,hUxW,M₀,hM₀,hmap⟩ := D.exists_local_normalizedWeightedBirkhoffMap_bound w φ
  obtain ⟨Ur,hUr,hφr,hroot⟩ := exists_local_sourceNormalizedActionRoot_uniform_lower hp hp1 φu
  obtain ⟨Ub,hUb,hφb,_,G,A,hG,hA,hbeta⟩ := D.angular.exists_local_uniform_betaCorrection_bound
    φu.val (D.source_subset (D.real_subset φu.property))
  let U := Ux ∩ normalizedWeightedSource w ⁻¹' (Ur ∩ Ub)
  have hU : IsOpen U := hUx.inter ((hUr.inter hUb).preimage (continuous_normalizedWeightedSource w))
  let C := 2*(Real.sqrt 8/2)*Real.exp A
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨U,hU,⟨hφx,hφr,hφb⟩,(fun ψ hψ => hUxW ψ hψ.1),C*(2*M₀),by positivity,?_⟩
  intro ψ hψ sign hsign
  let F := normalizedWeightedBirkhoffMap hp hp1 s w ψ
  have hm := hmap ψ hψ.1
  have hcoord := normalizedWeightedBirkhoffMap_apply_of_mem hp hp1 s w ψ hm.1.1 hm.1.2
  have hbound (n : ℤ) :
      ‖(w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign (normalizedWeightedSource w ψ)‖ ≤
        C*(‖F.1 n‖+‖F.2 n‖) := by
    have hrt := hroot _ hψ.2.1 n
    have hrne : sourceNormalizedActionRoot hp hp1 n (normalizedWeightedSource w ψ) ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hrt.1)
    have hb := norm_sourceGapWeightedEta_le_rectangular hp hp1 n s sign (normalizedWeightedSource w ψ)
      hsign 2 A (by norm_num) hrne hrt.2 ((hbeta _ hψ.2.2).2 n)
    have hxy := D.coordinates _ (hUxW ψ hψ.1) n
    have hx : F.1 n = (w (2*n):ℂ)*sourceBirkhoffX hp hp1 n s (normalizedWeightedSource w ψ) :=
      (hcoord n).1.trans (congrArg (fun z : ℂ => (w (2*n):ℂ)*z) hxy.1)
    have hy : F.2 n = (w (2*n):ℂ)*sourceBirkhoffY hp hp1 n s (normalizedWeightedSource w ψ) :=
      (hcoord n).2.trans (congrArg (fun z : ℂ => (w (2*n):ℂ)*z) hxy.2)
    rw [hx,hy,norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ ‖(w (2*n):ℂ)‖*(C*(‖sourceBirkhoffX hp hp1 n s (normalizedWeightedSource w ψ)‖+
          ‖sourceBirkhoffY hp hp1 n s (normalizedWeightedSource w ψ)‖)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨hmem,hnorm⟩ := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound _ F.1 F.2 C hC hbound
  refine ⟨hmem,hnorm.trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
  have h1 := (norm_fst_le F).trans hm.2
  have h2 := (norm_snd_le F).trans hm.2
  linarith

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
