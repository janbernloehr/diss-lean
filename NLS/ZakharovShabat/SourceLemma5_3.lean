import NLS.ZakharovShabat.SourceAbelianMomentOnePlusDomain
import NLS.ZakharovShabat.SourceSecondMomentMixed

/-! # Article Lemma 5.3 on one constructed original domain

The sharp off-diagonal estimate, including p = 2, and the fixed mixed
quadratic diagonal estimate hold on the same connected neighborhood.
The actual coefficients and every local neighborhood precede q > 1.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W W₀ V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The Hilbert endpoint uses the already checked refined row estimate,
whose lower exponent is exactly one. -/
theorem SourceAbelianMomentAtlas.exists_offDiagonal_onePlus_of_two_le
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s) (hp2 : 2 ≤ p)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ ψ ∈ U, ∃ T : Set (CoeffPair p),
        IsOpen T ∧ ψ ∈ T ∧ T ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
          ∀ χ ∈ T, ∀ n : ℤ, ∃ a : Coeff q,
            (∀ k, a k = sourceSecondMomentCubicCoefficient A n χ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
            ∀ k : ℤ, k ≠ n → A.moment n k 2 χ =
              (sourcePeriodicGapDisplacement hp hp1 χ k)^3/((n-k:ℤ):ℂ)*a k := by
  by_cases hgt : 2 < p
  · exact A.exists_offDiagonal_onePlus H hs hgt hV hrealV
  · have he : p = 2 := le_antisymm (not_lt.mp hgt) hp2
    have hhalf : ENNReal.ofReal (p.toReal/2) = 1 := by rw [he]; norm_num
    obtain ⟨U,hU,hUc,hreal,hUV,hlocal⟩ :=
      A.exists_almostReal_offDiagonal_secondMoment_coefficients hs hV hrealV
    refine ⟨U,hU,hUc,hreal,hUV,?_⟩
    intro ψ hψ
    obtain ⟨ρ,hρ,hball,hrows⟩ := hlocal ψ hψ
    refine ⟨ball ψ ρ,isOpen_ball,mem_ball_self hρ,hball,?_⟩
    intro q hq hq1
    exact hrows q hq hq1 (by rw [hhalf]; exact hq1.le)

/-- Both clauses of Lemma 5.3, retaining the literal off-diagonal
coefficient and the fixed diagonal mixed-exponent decomposition. -/
structure SourceLemma5_3Data (A : SourceAbelianMomentAtlas hp hp1 W s)
    (T : Set (CoeffPair p)) : Prop where
  mixed : SourceSecondMomentMixedData A T
  sharp_rows : ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
    ∀ ψ ∈ T, ∀ n : ℤ, ∃ a : Coeff q,
      (∀ k, a k = sourceSecondMomentCubicCoefficient A n ψ k) ∧ a n = 0 ∧ ‖a‖ ≤ M ∧
      ∀ k : ℤ, k ≠ n → A.moment n k 2 ψ =
        (sourcePeriodicGapDisplacement hp hp1 ψ k)^3/((n-k:ℤ):ℂ)*a k

/-- The source's literal q-power row bound is uniform in n and in
all sources of the selected common neighborhood. -/
theorem SourceLemma5_3Data.row_power_sum
    {A : SourceAbelianMomentAtlas hp hp1 W s} {T : Set (CoeffPair p)}
    (D : SourceLemma5_3Data A T) (q : ℝ≥0∞) (hq : q ≠ ⊤) (hq1 : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ T, ∀ n : ℤ,
      Summable (fun k => ‖sourceSecondMomentCubicCoefficient A n ψ k‖^q.toReal) ∧
      (∑' k : ℤ, ‖sourceSecondMomentCubicCoefficient A n ψ k‖^q.toReal) ≤ C := by
  obtain ⟨M,hM,hrows⟩ := D.sharp_rows q hq hq1
  have hqpos := ENNReal.toReal_pos (zero_lt_one.trans hq1).ne' hq
  refine ⟨(M+1)^q.toReal,Real.rpow_pos_of_pos (by positivity) _,?_⟩
  intro ψ hψ n
  obtain ⟨a,ha,_,hn,_⟩ := hrows ψ hψ n
  have he : sourceSecondMomentCubicCoefficient A n ψ = fun k => a k := (funext ha).symm
  rw [he]
  refine ⟨(lp.memℓp a).summable hqpos,?_⟩
  rw [← lp.norm_rpow_eq_tsum hqpos a]
  exact Real.rpow_le_rpow (lp.norm_nonneg' a) (hn.trans (by linarith)) hqpos.le

/-- The sharp row bounds and diagonal mixed decomposition share a domain
and a local neighborhood selected before every auxiliary exponent. -/
theorem SourceAbelianMomentAtlas.exists_lemma5_3
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (H : SourceLemma12_11Data hp hp1 W₀ V s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s) (hp2 : 2 ≤ p)
    (hV : IsOpen V) (hrealV : realTypeSourceLocus p ⊆ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
      U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ T : Set (CoeffPair p),
        IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ SourceLemma5_3Data A T := by
  obtain ⟨Uo,hUo,_,hrealO,hOV,hoff⟩ :=
    A.exists_offDiagonal_onePlus_of_two_le H hs hp2 hV hrealV
  obtain ⟨Ud,hUd,_,hrealD,_,hdiag⟩ := A.exists_lemma20_3_refined hs hV hrealV
  let S := Uo ∩ Ud
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealS : realTypeSourceLocus p ⊆ S := fun ψ hψ => ⟨hrealO hψ,hrealD hψ⟩
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := (hUo.inter hUd).connectedComponentIn
  refine ⟨U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS,
    fun ψ hψ => hOV (hUS hψ).1,?_⟩
  intro φ hφ
  obtain ⟨To,hTo,hφTo,_,ho⟩ := hoff φ (hUS hφ).1
  obtain ⟨ρ,hρ,_,hd⟩ := hdiag φ (hUS hφ).2
  let T := (To ∩ ball φ ρ) ∩ U
  have hmixed : SourceSecondMomentMixedData A T := by
    apply sourceSecondMomentMixedData_of_refined A T
    intro r hr hr1 hpr
    obtain ⟨M,hM,hb⟩ := hd r hr hr1 hpr
    exact ⟨M,hM,fun ψ hψ => hb ψ hψ.1.2⟩
  refine ⟨T,(hTo.inter isOpen_ball).inter hU,⟨⟨hφTo,mem_ball_self hρ⟩,hφ⟩,
    inter_subset_right,hmixed,?_⟩
  intro q hq hq1
  obtain ⟨M,hM,hb⟩ := ho q hq hq1
  exact ⟨M,hM,fun ψ hψ n => hb ψ hψ.1.1 n⟩

/-- Article Lemma 5.3, for every finite p ≥ 2, with all spectral data
constructed from the original normalized family. -/
theorem sourceLemma5_3 (hp : p ≠ ⊤) (hp2 : 2 ≤ p) :
    ∃ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourcePsiSquaredGapComplexExtension hp (lt_of_lt_of_le (by norm_num : (1:ℝ≥0∞)<2) hp2) V s ∧
      ∃ A : SourceAbelianMomentAtlas hp (lt_of_lt_of_le (by norm_num : (1:ℝ≥0∞)<2) hp2) W s,
        ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧
          U ⊆ A.domain ∩ V ∧ ∀ φ ∈ U, ∃ T : Set (CoeffPair p),
            IsOpen T ∧ φ ∈ T ∧ T ⊆ U ∧ SourceLemma5_3Data A T := by
  classical
  let hp1 : 1 < p := lt_of_lt_of_le (by norm_num : (1:ℝ≥0∞)<2) hp2
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 hp hp1
  have hs := H.angular_extension
  obtain ⟨W,_,_,hlocal⟩ := hs.toSourcePsiNormalizedComplexExtension.exists_moment_localCharts hV hrealV
  choose L hL using hlocal
  let A : SourceAbelianMomentAtlas hp hp1 W s := ⟨L⟩
  obtain ⟨U,hU,hUc,hreal,hUV,hrows⟩ := A.exists_lemma5_3 H.previous hs hp2 hV hrealV
  exact ⟨W,V,s,hs,A,U,hU,hUc,hreal,hUV,hrows⟩

end NLS.ZakharovShabat
