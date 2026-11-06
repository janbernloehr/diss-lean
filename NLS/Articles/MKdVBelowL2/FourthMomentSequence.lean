import NLS.Articles.MKdVBelowL2.FourthMomentAnalytic
import NLS.ZakharovShabat.SourceFrequencySequenceBounds
import NLS.SequenceSpaces.WeightedIndexRealization

/-! # Analytic weighted sequence targets for the H₄ candidate

An exact weighted-sum identity reduces the candidate to the established
unweighted moment sequence plus a uniformly bounded correction. Thus the
candidate is analytic into ℓ^(-1,r) for finite r > 1 with r ≥ p/2.
This concerns the actual moment candidate before physical H₄ identification.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The weighted candidate differs from 6πn times the unweighted candidate
by a bounded cubic product; both constants follow from their literal sums. -/
theorem fourthFrequencyCandidate_difference_bound
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) (n : ℤ)
    (a : Coeff p.conjExponent) (han : a n = 0)
    (hrow : ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k)
    (hs : Summable (fun k => A.moment n k 2 ψ))
    (hw : Summable (fun k : ℤ => (k:ℂ)*A.moment n k 2 ψ)) :
    ‖fourthFrequencyCandidate A n ψ-(6*Real.pi:ℂ)*(n:ℂ)*A.renormalizedFrequency n ψ‖ ≤
      12*‖sourcePeriodicGapDisplacement hp hp1 ψ‖^3*‖a‖ := by
  have h := Coeff.norm_weighted_tsum_sub_index_tsum_le hp hp1
    (sourcePeriodicGapDisplacement hp hp1 ψ) a n (fun k => A.moment n k 2 ψ) han hrow hs hw
  have he : fourthFrequencyCandidate A n ψ-(6*Real.pi:ℂ)*(n:ℂ)*A.renormalizedFrequency n ψ =
      (-12:ℂ)*((∑' k : ℤ, (k:ℂ)*A.moment n k 2 ψ)-(n:ℂ)*(∑' k, A.moment n k 2 ψ)) := by
    unfold fourthFrequencyCandidate SourceAbelianMomentAtlas.renormalizedFrequency
    have hπ : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  rw [he,norm_mul]
  norm_num only [norm_neg,Complex.norm_ofNat]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ)≤12)

/-- The actual weighted sequence realization, with values fixed below on
its constructed source domain. -/
def fourthFrequencySequence (A : SourceAbelianMomentAtlas hp hp1 W s)
    (r : ℝ≥0∞) [Fact (1 ≤ r)] (ψ : CoeffPair p) : WeightedCoeff (Weight.sobolev (-1)) r :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev (-1)) r (fun n => fourthFrequencyCandidate A n ψ)

/-- One common domain supports analyticity in every target required by
Theorem 1.3, including all finite r > 1 at the Hilbert exponent. -/
theorem exists_analytic_fourthFrequencySequence
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧
      (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖)) ∧
      ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        (∀ ψ ∈ U, ∀ n, (fourthFrequencySequence A r ψ).val n = fourthFrequencyCandidate A n ψ) ∧
          AnalyticOnNhd ℂ (fourthFrequencySequence A r) U := by
  obtain ⟨Uo,hUo,_,hrealO,_,hoff⟩ := A.exists_offDiagonal_onePlus_all H hs hV hrealV
  obtain ⟨Uc,hUc,_,hrealC,hCV,hw,ha⟩ := exists_analytic_fourthFrequencyCandidate A H hs hV hrealV
  obtain ⟨Uf,hUf,_,hrealF,_,hunw,_,_⟩ := A.exists_analytic_renormalizedFrequency hs hV hrealV
  obtain ⟨Us,hUs,_,hrealS,_,_,hseq⟩ := A.exists_frequencySequence_neighborhood hs hV hrealV
  let S := ((Uo ∩ Uc) ∩ Uf) ∩ Us
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hreal : realTypeSourceLocus p ⊆ S := fun ψ hψ =>
    ⟨⟨⟨hrealO hψ,hrealC hψ⟩,hrealF hψ⟩,hrealS hψ⟩
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := ((hUo.inter hUc).inter hUf).inter hUs |>.connectedComponentIn
  have hlocal (φ : CoeffPair p) (hφ : φ ∈ U) :
      ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧
        ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ T,
            ∃ b : WeightedCoeff (Weight.sobolev (-1)) r,
              (∀ n, b.val n = fourthFrequencyCandidate A n ψ) ∧ ‖b‖ ≤ B := by
    have hpc1 : 1 < p.conjExponent :=
      (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    have hpc : p.conjExponent ≠ ⊤ :=
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
    let : Fact (1 ≤ p.conjExponent) := ⟨hpc1.le⟩
    obtain ⟨To,hTo,hφo,_,ho⟩ := hoff φ (hUS hφ).1.1.1
    obtain ⟨M,hM,hrows⟩ := ho p.conjExponent hpc hpc1
    obtain ⟨Tb,hTb,hφb,_,hb⟩ := hseq φ (hUS hφ).2
    obtain ⟨_,_,Tg,hTg,hφg,G,hG,hg⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
    let T := ((To ∩ Tb) ∩ Tg) ∩ U
    refine ⟨T,((hTo.inter hTb).inter hTg).inter hU,⟨⟨⟨hφo,hφb⟩,hφg⟩,hφ⟩,
      inter_subset_right,?_⟩
    intro r inst hr hr1 hpr
    obtain ⟨B,hB,hbound⟩ := hb r hr hr1 hpr
    refine ⟨‖(6*Real.pi:ℂ)‖*B+(12*G^3*M)*‖Coeff.inverseBracketCoeffs r hr1‖,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨heq,hbn⟩ := hbound ψ hψ.1.1.2
    have hdiff (n : ℤ) :
        ‖fourthFrequencyCandidate A n ψ-(6*Real.pi:ℂ)*(n:ℂ)*A.frequencySequence r ψ n‖ ≤ 12*G^3*M := by
      obtain ⟨a,_,han,hn,hrf⟩ := hrows ψ hψ.1.1.1 n
      rw [heq n]
      apply (fourthFrequencyCandidate_difference_bound A ψ n a han hrf
        (hunw ψ (hUS hψ.2).1.2 n).of_norm (hw ψ (hUS hψ.2).1.1.2 n).of_norm).trans
      gcongr
      exact (hg ψ hψ.1.2).1
    obtain ⟨b,hb,hbnorm⟩ := Coeff.exists_negOne_weighted_of_bounded_error hr1
      (fun n => fourthFrequencyCandidate A n ψ) (A.frequencySequence r ψ) (6*Real.pi:ℂ)
      (12*G^3*M) (by positivity) hdiff
    exact ⟨b,hb,hbnorm.trans (add_le_add
      (mul_le_mul_of_nonneg_left hbn (norm_nonneg _)) le_rfl)⟩
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hreal hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hreal,
    fun ψ hψ => hCV (hUS hψ).1.1.2,
    fun ψ hψ n => hw ψ (hUS hψ).1.1.2 n,?_⟩
  intro r inst hr hr1 hpr
  have hcoords (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      ∀ n, (fourthFrequencySequence A r ψ).val n = fourthFrequencyCandidate A n ψ := by
    obtain ⟨T,_,hψT,_,hb⟩ := hlocal ψ hψ
    obtain ⟨_,_,hb⟩ := hb r hr hr1 hpr
    obtain ⟨b,hb,_⟩ := hb ψ hψT
    change ∀ n, (WeightedCoeff.ofFunctionOrZero _ _ _).val n = _
    rw [WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ b hb]
    exact hb
  refine ⟨hcoords,?_⟩
  intro φ hφ
  obtain ⟨T,hT,hφT,hTU,hb⟩ := hlocal φ hφ
  obtain ⟨B,_,hb⟩ := hb r hr hr1 hpr
  exact (WeightedCoeff.analytic_realization_of_bound (Weight.sobolev (-1))
    (fun ψ n => fourthFrequencyCandidate A n ψ) hT
    (fun n ψ hψ => ha n ψ (hUS (hTU hψ)).1.1.2) B hb).1 φ hφT

/-- Construct the scalar and weighted-sequence analytic candidates together
from the same original root family at every finite p > 1. -/
theorem exists_fourthMoment_sequenceAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 V s ∧
        ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧
          (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖)) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fourthFrequencyCandidate A n) U) ∧
          ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
            (∀ ψ ∈ U, ∀ n, (fourthFrequencySequence A r ψ).val n = fourthFrequencyCandidate A n ψ) ∧
              AnalyticOnNhd ℂ (fourthFrequencySequence A r) U := by
  classical
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 hp hp1
  have hs := H.angular_extension
  obtain ⟨W,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  obtain ⟨U,hU,hUc,hreal,hUV,hconv,hseq⟩ := exists_analytic_fourthFrequencySequence A H.previous hs hV hrealV
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨he,ha⟩ := hseq p hp hp1 hhalf
  refine ⟨W,V,hV,hrealV,s,hs,A,U,hU,hUc,hreal,hUV,hconv,?_,hseq⟩
  intro n ψ hψ
  apply (((WeightedCoeff.evalCLM (Weight.sobolev (-1)) p n).analyticAt _).comp (ha ψ hψ)).congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  exact he χ hχ n

end NLS.Articles.MKdVBelowL2
