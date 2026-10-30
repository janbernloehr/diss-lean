import NLS.ZakharovShabat.SourceActionGapCorrection
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-!
# The quarter-exponent action-gap remainder

The p/2 normalized-action deviation multiplied by the squared gap gives
the p/4 remainder on p.96. All target bounds share one neighborhood.
The resulting mixed decomposition is fixed before its OnePlus exponent.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual action-gap correction has locally uniform bounds at every
finite r>1 with r>=p/4, on a neighborhood chosen before r and all indices. -/
theorem exists_local_sourceActionGapQuarter (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧
      (∀ n, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) T) ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/4) ≤ r →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
          (∀ n, b n = sourceActionGapCorrection hp hp1 ψ n) ∧ ‖b‖ ≤ C := by
  obtain ⟨V,hV,hφV,hA,hcoarse⟩ := exists_local_sourceActionGapCorrection hp hp1 φ hφ
  by_cases hp2 : p ≤ 2
  · refine ⟨V,hV,hφV,hA,?_⟩
    intro r hr hr1 _
    apply hcoarse r hr hr1
    have hpr : p.toReal ≤ 2 := by
      simpa using ENNReal.toReal_mono (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hp2
    have ht : ENNReal.ofReal (p.toReal/3) ≤ 1 := by
      rw [ENNReal.ofReal_le_iff_le_toReal (by norm_num)]
      norm_num
      linarith
    exact ht.trans hr1.le
  · have hp2' : 2 < p := lt_of_not_ge hp2
    have hpr : 2 < p.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) hp).mpr hp2'
    let q := ENNReal.ofReal (p.toReal/2)
    have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
    have hqr : q.toReal = p.toReal/2 := ENNReal.toReal_ofReal (by positivity)
    have hq1 : 1 < q := by
      apply (ENNReal.toReal_lt_toReal (by norm_num) hqt).mp
      rw [hqr]
      norm_num
      linarith
    let : Fact (1 ≤ q) := ⟨hq1.le⟩
    obtain ⟨B,hB,hφB,M,hbound⟩ :=
      exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm hp hp1 hq1 hqt le_rfl φ hφ
    obtain ⟨F,hF,hφF,_,hfactor⟩ :=
      exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ hφ
    obtain ⟨G,hG,hφG,R,hR,hgap⟩ := exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
    have hM : 0 ≤ M := by
      obtain ⟨a,_,ha⟩ := hbound φ hφB
      exact (norm_nonneg a).trans ha
    let T := V ∩ (B ∩ (F ∩ G))
    refine ⟨T,hV.inter (hB.inter (hF.inter hG)),⟨hφV,hφB,hφF,hφG⟩,
      fun n => (hA n).mono (fun _ h => h.1),?_⟩
    intro r hr hr1 hpr4
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    have hqr4 : ENNReal.ofReal (q.toReal/2) ≤ r := by
      rw [hqr,show p.toReal/2/2 = p.toReal/4 by ring]
      exact hpr4
    refine ⟨R^2*M/4,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨a,ha,hanorm⟩ := hbound ψ hψ.2.1
    let g : Coeff q := sourcePeriodicSquaredGapCoeff hp hp1 ψ
    obtain ⟨H,hH,hHnorm⟩ := Coeff.exists_refined_product_majorant hqt
      (zero_lt_one.trans hq1) hr (zero_lt_one.trans hr1) hqr4 g a
    have hdom (n : ℤ) : ‖g n*a n‖ ≤ ‖H n‖ := by simpa only [norm_mul] using hH n
    have hmem : Memℓp (fun n : ℤ => g n*a n) r := by
      apply (lp.memℓp H).mono'
      exact hdom
    let b : Coeff r := ⟨fun n => g n*a n,hmem⟩
    have hb : ‖b‖ ≤ R^2*M := by
      apply (lp.norm_mono (zero_lt_one.trans hr1).ne' hdom).trans
      apply hHnorm.trans
      exact mul_le_mul (hgap ψ hψ.2.2.2) hanorm (norm_nonneg _) (sq_nonneg _)
    refine ⟨(1/4:ℂ) • b,?_,?_⟩
    · intro n
      change (1/4:ℂ)*(g n*a n) = _
      rw [ha n]
      dsimp only [g]
      rw [sourcePeriodicSquaredGapCoeff_apply]
      simp only [sourceActionGapCorrection,sourceNormalizedActionDeviation,hfactor ψ hψ.2.2.1 n]
      ring
    · rw [norm_smul]
      norm_num
      linarith

/-- The sharper bounds hold on a connected neighborhood of the whole real
locus inside any prescribed open source neighborhood of that locus. -/
theorem exists_sourceActionGapQuarter_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ V ∧
      (∀ n, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/4) ≤ r →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
            (∀ n, b n = sourceActionGapCorrection hp hp1 ψ n) ∧ ‖b‖ ≤ C := by
  classical
  choose T hT hφT hA hb using fun φ : realTypeSourceLocus p =>
    exists_local_sourceActionGapQuarter hp hp1 φ.val φ.property
  let S := (⋃ φ : realTypeSourceLocus p, T φ) ∩ V
  have hS : IsOpen S := (isOpen_iUnion hT).inter hV
  have hrealS : realTypeSourceLocus p ⊆ S := fun φ hφ =>
    ⟨mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφT _⟩,hrealV hφ⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset _ _
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,
    fun _ h => (hUS h).2,?_,?_⟩
  · intro n ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ).1
    exact hA φ n ψ hψT
  · intro ψ hψ
    obtain ⟨φ,hψT⟩ := mem_iUnion.mp (hUS hψ).1
    refine ⟨T φ ∩ U,(hT φ).inter hU,⟨hψT,hψ⟩,fun _ h => h.2,?_⟩
    intro r hr hr1 hpr
    obtain ⟨C,hC,hbound⟩ := hb φ r hr hr1 hpr
    exact ⟨C,hC,fun χ hχ => hbound χ hχ.1⟩

/-- The literal p/4 plus OnePlus remainder on p.96. Its two summands are
fixed before every OnePlus projection exponent; all signed and collapsed
gaps are included on a common complex neighborhood inside V. -/
theorem exists_sourceActionGapQuarter_mixed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ V ∧
      (∀ n, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) U) ∧
      ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∃ a : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/4)),
        ∃ b : CoeffPair p → CoeffOnePlus,
          (∀ ψ ∈ T, ∀ n, (sourcePeriodicGapDisplacement hp hp1 ψ n)^2/4 =
            sourceComplexAction hp hp1 n ψ + a ψ n + (b ψ).1 n) ∧
          (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖a ψ‖ ≤ C) ∧
          ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
            ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b ψ)‖ ≤ C := by
  obtain ⟨U,hU,hUc,hreal,hUV,hA,hlocal⟩ :=
    exists_sourceActionGapQuarter_neighborhood hp hp1 V hV hrealV
  refine ⟨U,hU,hUc,hreal,hUV,hA,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,hb⟩ := hlocal φ hφ
  have hneg : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/4) ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
        (∀ n, b n = -sourceActionGapCorrection hp hp1 ψ n) ∧ ‖b‖ ≤ C := by
    intro r hr hr1 hpr
    obtain ⟨C,hC,hbound⟩ := hb r hr hr1 hpr
    refine ⟨C,hC,?_⟩
    intro ψ hψ
    obtain ⟨b,he,hbnorm⟩ := hbound ψ hψ
    exact ⟨-b,fun n => by simpa only [lp.coeFn_neg,Pi.neg_apply] using congrArg Neg.neg (he n),
      by simpa only [lp.norm_neg] using hbnorm⟩
  obtain ⟨a,b,he,ha,hb⟩ := Coeff.exists_onePlus_decomposition_of_refined T
    (fun ψ n => -sourceActionGapCorrection hp hp1 ψ n) ENNReal.ofReal_ne_top hneg
  refine ⟨T,hT,hφT,hTU,a,b,?_,ha,hb⟩
  intro ψ hψ n
  have h := he ψ hψ n
  dsimp only [sourceActionGapCorrection] at h
  linear_combination h

end NLS.ZakharovShabat
