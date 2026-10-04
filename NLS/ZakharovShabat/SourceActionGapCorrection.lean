import NLS.SequenceSpaces.RefinedTripleProduct
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceSquaredGapNorm

/-! # Replacing the leading squared gap by the actual action

The exact normalized-action factorization gives a cubic product bound
for I_n - gamma_n^2/4. A common connected almost-real domain supports
all target exponents r > 1 with r >= p/3, with local neighborhoods
chosen before r. This is the input for equation (4.12).
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The difference between the actual action and its leading squared gap. -/
def sourceActionGapCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceComplexAction hp hp1 n ψ - (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/4

/-- Near every real source the action correction is uniformly bounded
in all the refined target spaces on one common source neighborhood. -/
theorem exists_local_sourceActionGapCorrection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧
      (∀ n, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) T) ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
          (∀ n, b n = sourceActionGapCorrection hp hp1 ψ n) ∧ ‖b‖ ≤ C := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨B,hB,hφB,M,hbound⟩ :=
    exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm hp hp1 hp1 hp hhalf φ hφ
  obtain ⟨F,hF,hφF,hfactorA,hfactor⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ hφ
  obtain ⟨G,hG,_,hrealG,hgapA⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨_,_,H,hH,hφH,R,hR,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  have hM : 0 ≤ M := by
    obtain ⟨a,_,ha⟩ := hbound φ hφB
    exact (norm_nonneg a).trans ha
  let T := (B ∩ F) ∩ (G ∩ H)
  have hT : IsOpen T := (hB.inter hF).inter (hG.inter hH)
  refine ⟨T,hT,⟨⟨hφB,hφF⟩,hrealG hφ,hφH⟩,?_,?_⟩
  · intro n ψ hψ
    have ha : AnalyticAt ℂ (fun χ => (sourcePeriodicGapDisplacement hp hp1 χ n)^2) ψ := by
      simpa only [sourcePeriodicGapDisplacement_apply] using (hgapA ψ hψ.2.1 n).2
    apply (ha.mul (hfactorA n ψ hψ.1.2)).congr
    filter_upwards [hT.mem_nhds hψ] with χ hχ
    exact (hfactor χ hχ.1.2 n).symm
  · intro r hr hr1 hpr
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    refine ⟨R^2*M/4,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨a,haval,hanorm⟩ := hbound ψ hψ.1.1
    let g := sourcePeriodicGapDisplacement hp hp1 ψ
    obtain ⟨b,hb,hbnorm⟩ := Coeff.exists_refined_triple_product hp (zero_lt_one.trans hp1)
      hr (zero_lt_one.trans hr1) hpr g g a
    refine ⟨(1/4:ℂ) • b,?_,?_⟩
    · intro n
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hb n,haval n,
        sourceActionGapCorrection,sourceNormalizedActionDeviation,hfactor ψ hψ.1.2 n]
      dsimp [g]
      ring
    · rw [norm_smul]
      norm_num
      have hn : ‖b‖ ≤ R^2*M := by
        apply hbnorm.trans
        calc
          _ ≤ R*R*M := by gcongr <;> exact (hgap ψ hψ.2.2).1
          _ = _ := by ring
      linarith

/-- One connected neighborhood of the entire real locus carries the
actual scalar actions and the locally uniform refined correction. -/
theorem exists_sourceActionGapCorrection_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      (∀ n, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = sourceActionGapCorrection hp hp1 ψ n) ∧ ‖b‖ ≤ C := by
  classical
  choose T hT hφT hA hb using fun φ : realTypeSourceLocus p =>
    exists_local_sourceActionGapCorrection hp hp1 φ.val φ.property
  let S := ⋃ φ : realTypeSourceLocus p, T φ
  have hS : IsOpen S := isOpen_iUnion hT
  have hrealS : realTypeSourceLocus p ⊆ S := fun φ hφ => mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφT _⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset _ _
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_⟩
  · intro n ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ)
    exact hA φ n ψ hψT
  · intro ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ)
    refine ⟨T φ ∩ U,(hT φ).inter hU,⟨hψT,hψ⟩,fun _ h => h.2,?_⟩
    intro r hr hr1 hpr
    obtain ⟨C,hC,hb⟩ := hb φ r hr hr1 hpr
    exact ⟨C,hC,fun χ hχ => hb χ hχ.1⟩

end NLS.ZakharovShabat
