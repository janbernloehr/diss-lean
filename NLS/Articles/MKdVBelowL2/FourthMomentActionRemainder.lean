import NLS.Articles.MKdVBelowL2.FourthMomentSequence
import NLS.ZakharovShabat.SourceActionFrequencyCorrection

/-! # Refined actual-action remainder of the H₄ candidate

The bounded difference from 6πn times the unweighted moment frequency
and the established action correction give a fixed ℓ^(p/3)+ℓ^(1+)
remainder. Division by the index is totalized at zero; reconstruction
keeps the actual zero coordinate as an explicit finite-coordinate term.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The normalized actual-action remainder; its zero coordinate is zero. -/
def fourthActionRemainder (A : SourceAbelianMomentAtlas hp hp1 W s)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  (fourthFrequencyCandidate A n ψ+(12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n ψ)/(n:ℂ)

@[simp] theorem fourthActionRemainder_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) :
    fourthActionRemainder A ψ 0 = 0 := by
  simp only [fourthActionRemainder,Int.cast_zero,div_zero]

/-- The asymptotic reconstruction is exact at nonzero indices and explicitly
retains the actual candidate at zero. No zero-frequency vanishing is assumed. -/
theorem fourthActionRemainder_reconstruct
    (A : SourceAbelianMomentAtlas hp hp1 W s) (ψ : CoeffPair p) (n : ℤ) :
    fourthFrequencyCandidate A n ψ+(12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n ψ =
      (n:ℂ)*fourthActionRemainder A ψ n+(if n=0 then fourthFrequencyCandidate A 0 ψ else 0) := by
  by_cases hn : n=0
  · subst n
    simp only [Int.cast_zero,mul_zero,zero_mul,add_zero,ite_true,zero_add]
  · have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [fourthActionRemainder,if_neg hn,add_zero]
    field_simp

/-- Refined realizations and one fixed genuine mixed decomposition on T.
The same maps are chosen before every OnePlus projection exponent. -/
structure FourthActionRemainderData (A : SourceAbelianMomentAtlas hp hp1 W s)
    (T : Set (CoeffPair p)) : Prop where
  refined : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
      (∀ n, b n = fourthActionRemainder A ψ n) ∧ ‖b‖ ≤ C
  mixed : ∃ a : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/3)),
    ∃ b : CoeffPair p → CoeffOnePlus,
      (∀ ψ ∈ T, ∀ n, fourthActionRemainder A ψ n = a ψ n+(b ψ).1 n) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖a ψ‖ ≤ C) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b ψ)‖ ≤ C

/-- The actual candidate has the refined action remainder on one connected
complex neighborhood of the entire real source space. -/
theorem exists_fourthActionRemainder
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ T : Set (CoeffPair p),
        IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ FourthActionRemainderData A T := by
  obtain ⟨Uo,hUo,_,hrealO,_,hoff⟩ := A.exists_offDiagonal_onePlus_all H hs hV hrealV
  obtain ⟨Uc,hUc,_,hrealC,hCV,hw,_⟩ := exists_analytic_fourthFrequencyCandidate A H hs hV hrealV
  obtain ⟨Uf,hUf,_,hrealF,_,hunw,_,_⟩ := A.exists_analytic_renormalizedFrequency hs hV hrealV
  obtain ⟨Ua,hUa,_,hrealA,_,_,hact⟩ := A.exists_actionFrequencyCorrection_neighborhood hs hV hrealV
  let S := ((Uo ∩ Uc) ∩ Uf) ∩ Ua
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hreal : realTypeSourceLocus p ⊆ S := fun ψ hψ =>
    ⟨⟨⟨hrealO hψ,hrealC hψ⟩,hrealF hψ⟩,hrealA hψ⟩
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := ((hUo.inter hUc).inter hUf).inter hUa |>.connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hreal hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hreal,
    fun ψ hψ => hCV (hUS hψ).1.1.2,?_⟩
  intro φ hφ
  have hpc1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hpc1.le⟩
  obtain ⟨To,hTo,hφo,_,ho⟩ := hoff φ (hUS hφ).1.1.1
  obtain ⟨M,hM,hrows⟩ := ho p.conjExponent hpc hpc1
  obtain ⟨Ta,hTa,hφa,_,ha⟩ := hact φ (hUS hφ).2
  obtain ⟨_,_,Tg,hTg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  let T := ((To ∩ Ta) ∩ Tg) ∩ U
  have hb : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
        (∀ n, b n = fourthActionRemainder A ψ n) ∧ ‖b‖ ≤ C := by
    intro r hr hr1 hpr
    let : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨B,hB,hbound⟩ := ha r hr hr1 hpr
    refine ⟨‖(6*Real.pi:ℂ)‖*B+(12*G^3*M)*‖Coeff.puncturedLattice r hr1‖,by positivity,?_⟩
    intro ψ hψ
    obtain ⟨b,hb,hbn⟩ := hbound ψ hψ.1.1.2
    have hdiff (n : ℤ) :
        ‖(fourthFrequencyCandidate A n ψ+(12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n ψ)-
          (6*Real.pi:ℂ)*(n:ℂ)*b n‖ ≤ 12*G^3*M := by
      obtain ⟨a,_,han,hn,hrf⟩ := hrows ψ hψ.1.1.1 n
      have he : (fourthFrequencyCandidate A n ψ+(12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n ψ)-
          (6*Real.pi:ℂ)*(n:ℂ)*b n =
          fourthFrequencyCandidate A n ψ-(6*Real.pi:ℂ)*(n:ℂ)*A.renormalizedFrequency n ψ := by
        rw [hb n]
        unfold SourceAbelianMomentAtlas.actionFrequencyCorrection
        ring
      rw [he]
      apply (fourthFrequencyCandidate_difference_bound A ψ n a han hrf
        (hunw ψ (hUS hψ.2).1.2 n).of_norm (hw ψ (hUS hψ.2).1.1.2 n).of_norm).trans
      gcongr
      exact (hg ψ hψ.1.2).1
    obtain ⟨c,hc,hcn⟩ := Coeff.exists_index_quotient_of_bounded_error hr1
      (fun n => fourthFrequencyCandidate A n ψ+(12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n ψ)
      b (6*Real.pi:ℂ) (12*G^3*M) (by positivity) hdiff
    exact ⟨c,hc,hcn.trans (add_le_add (mul_le_mul_of_nonneg_left hbn (norm_nonneg _)) le_rfl)⟩
  refine ⟨T,((hTo.inter hTa).inter hTg).inter hU,⟨⟨⟨hφo,hφa⟩,hφg⟩,hφ⟩,
    inter_subset_right,hb,?_⟩
  exact Coeff.exists_onePlus_decomposition_of_refined T (fourthActionRemainder A) ENNReal.ofReal_ne_top hb

/-- Construct one actual atlas supporting convergence, weighted analyticity
and the refined actual-action remainder on a common source domain. -/
theorem exists_fourthMoment_refinedAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 V s ∧
        ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧
          (∀ ψ ∈ U, ∀ n : ℤ, Summable (fun k : ℤ => ‖(k:ℂ)*A.moment n k 2 ψ‖)) ∧
          (∀ n : ℤ, AnalyticOnNhd ℂ (fourthFrequencyCandidate A n) U) ∧
          (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
            (∀ ψ ∈ U, ∀ n, (fourthFrequencySequence A r ψ).val n = fourthFrequencyCandidate A n ψ) ∧
              AnalyticOnNhd ℂ (fourthFrequencySequence A r) U) ∧
          ∀ φ ∈ U, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ FourthActionRemainderData A T := by
  classical
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 hp hp1
  have hs := H.angular_extension
  obtain ⟨W,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  obtain ⟨Us,hUs,_,hrealS,hSV,hconv,hseq⟩ := exists_analytic_fourthFrequencySequence A H.previous hs hV hrealV
  obtain ⟨Ur,hUr,_,hrealR,_,hrem⟩ := exists_fourthActionRemainder A H.previous hs hV hrealV
  let U := connectedComponentIn (Us ∩ Ur) (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hreal : realTypeSourceLocus p ⊆ Us ∩ Ur := fun ψ hψ => ⟨hrealS hψ,hrealR hψ⟩
  have hUS : U ⊆ Us ∩ Ur := connectedComponentIn_subset _ _
  have hU : IsOpen U := (hUs.inter hUr).connectedComponentIn
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp]
    exact ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := p)])
  obtain ⟨he,ha⟩ := hseq p hp hp1 hhalf
  refine ⟨W,V,hV,hrealV,s,hs,A,U,hU,isConnected_connectedComponentIn_iff.mpr (hreal hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hreal,
    fun ψ hψ => hSV (hUS hψ).1,fun ψ hψ n => hconv ψ (hUS hψ).1 n,?_,?_,?_⟩
  · intro n ψ hψ
    apply (((WeightedCoeff.evalCLM (Weight.sobolev (-1)) p n).analyticAt _).comp (ha ψ (hUS hψ).1)).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact he χ (hUS hχ).1 n
  · intro r inst hr hr1 hpr
    obtain ⟨he,ha⟩ := hseq r hr hr1 hpr
    exact ⟨fun ψ hψ n => he ψ (hUS hψ).1 n,ha.mono (fun ψ hψ => (hUS hψ).1)⟩
  · intro φ hφ
    obtain ⟨T,hT,hφT,_,hb⟩ := hrem φ (hUS hφ).2
    refine ⟨T ∩ U,hT.inter hU,⟨hφT,hφ⟩,inter_subset_right,?_,?_⟩
    · intro r hr hr1 hpr
      obtain ⟨C,hC,hb⟩ := hb.refined r hr hr1 hpr
      exact ⟨C,hC,fun ψ hψ => hb ψ hψ.1⟩
    · obtain ⟨a,b,he,ha,hb⟩ := hb.mixed
      exact ⟨a,b,fun ψ hψ n => he ψ hψ.1 n,
        (by obtain ⟨C,hC,ha⟩ := ha; exact ⟨C,hC,fun ψ hψ => ha ψ hψ.1⟩),
        fun q hq1 hq => by obtain ⟨C,hC,hb⟩ := hb q hq1 hq; exact ⟨C,hC,fun ψ hψ => hb ψ hψ.1⟩⟩

end NLS.Articles.MKdVBelowL2
