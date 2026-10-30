import NLS.FunctionalAnalysis.ContractibleProjectionNeighborhood
import NLS.SequenceSpaces.RealCoeffNorm
import NLS.ZakharovShabat.SourceRealTypeProjection
import NLS.ZakharovShabat.SourcePsiOriginalOmegaContractible

/-!
# A contractible complex neighborhood of the original real domain

The joint real projection is nonexpansive and fixes the isometrically embedded original real domain.
-/

noncomputable section
namespace NLS.ZakharovShabat
open Set Complex Metric
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiOriginalRealEmbedding (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    realTypeSourceSubmodule p × RealCoeff p → Coeff p × CoeffPair p :=
  fun t => (RealCoeff.complexCLM p t.2,(t.1:CoeffPair p))

def sourcePsiOriginalRealProjection (hp : p ≠ ⊤) :
    Coeff p × CoeffPair p → realTypeSourceSubmodule p × RealCoeff p :=
  fun t => (sourceRealTypeProjection hp t.2,Coeff.reCLM p t.1)

theorem isometry_sourcePsiOriginalRealEmbedding :
    Isometry (sourcePsiOriginalRealEmbedding p) := by
  apply Isometry.of_dist_eq
  intro x y
  dsimp only [sourcePsiOriginalRealEmbedding]
  rw [Prod.dist_eq,Prod.dist_eq,Subtype.dist_eq]
  simp only [dist_eq_norm]
  rw [← map_sub,RealCoeff.norm_complexCLM]
  exact max_comm _ _

theorem continuous_sourcePsiOriginalRealProjection (hp : p ≠ ⊤) :
    Continuous (sourcePsiOriginalRealProjection hp) :=
  ((sourceRealTypeProjection hp).continuous.comp continuous_snd).prodMk
    ((Coeff.reCLM p).continuous.comp continuous_fst)

theorem sourcePsiOriginalRealProjection_embedding (hp : p ≠ ⊤)
    (t : realTypeSourceSubmodule p × RealCoeff p) :
    sourcePsiOriginalRealProjection hp (sourcePsiOriginalRealEmbedding p t) = t := by
  simp only [sourcePsiOriginalRealEmbedding,sourcePsiOriginalRealProjection,
    sourceRealTypeProjection_subtype,RealCoeff.reCLM_complexCLM]

theorem lipschitzWith_sourcePsiOriginalJointRealPart (hp : p ≠ ⊤) :
    LipschitzWith 1 (sourcePsiOriginalRealEmbedding p ∘ sourcePsiOriginalRealProjection hp) := by
  have hnorm (a : Coeff p) : ‖Coeff.reCLM p a‖ ≤ ‖a‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro n
    simpa only [Coeff.reCLM_apply,Real.norm_eq_abs] using Complex.abs_re_le_norm (a n)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,Function.comp_apply,sourcePsiOriginalRealEmbedding,
    sourcePsiOriginalRealProjection,Prod.dist_eq,sourceRealTypeProjection_val]
  apply max_le_max
  · rw [dist_eq_norm,dist_eq_norm,← map_sub,RealCoeff.norm_complexCLM,← map_sub]
    exact hnorm (x.1-y.1)
  · simpa only [NNReal.coe_one,one_mul] using (lipschitzWith_sourceRealPart hp).dist_le_mul x.2 y.2

/-- The entire original real domain has a contractible complex
thickening inside any prescribed open neighborhood of it. -/
theorem exists_contractible_complex_neighborhood_originalOmega
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : realTypeSourceSubmodule p → Set (CoeffPair p))
    (D : realTypeSourceSubmodule p → ℤ → Set ℂ)
    (c : realTypeSourceSubmodule p → ℝ)
    (hD : ∀ φ, SourceIsolatingNeighborhoods hp hp1 (V φ) (D φ) (c φ))
    (hVopen : ∀ φ, IsOpen (V φ)) (hV : ∀ φ, (φ:CoeffPair p) ∈ V φ)
    (G : Set (Coeff p × CoeffPair p)) (hG : IsOpen G)
    (hAG : sourcePsiOriginalRealEmbedding p '' (⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)) ⊆ G) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      sourcePsiOriginalRealEmbedding p '' (⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)) ⊆ U ∧
      U ⊆ G ∧ ContractibleSpace U := by
  let A := ⋃ φ, sourcePsiOriginalOmega (V φ) (D φ)
  let : ContractibleSpace A := contractible_iUnion_sourcePsiOriginalOmega hp hp1 V D c hD hV
  exact NLS.FunctionalAnalysis.exists_contractible_open_neighborhood_of_isometric_retract
    (sourcePsiOriginalRealEmbedding p) isometry_sourcePsiOriginalRealEmbedding
    (sourcePsiOriginalRealProjection hp) (continuous_sourcePsiOriginalRealProjection hp)
    (sourcePsiOriginalRealProjection_embedding hp) (lipschitzWith_sourcePsiOriginalJointRealPart hp)
    A (isOpen_iUnion (fun φ => (hD φ).isOpen_originalOmega (hVopen φ))) G hG hAG

end NLS.ZakharovShabat
