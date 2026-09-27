import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceContinuity
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedPositive
import NLS.SequenceSpaces.CoefficientDecay

/-!
# Uniform positive real part of normalized actions

Norm continuity of the complex normalized-action deviation makes its
distant coordinates close to those of a fixed real-type base source.
Those base coordinates tend to zero. The finitely many remaining
normalized actions have positive real part by the real-type theorem,
so one smaller complex neighborhood has a common positive lower bound
for every signed index.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real-type source, all complex normalized actions have real
part uniformly bounded away from zero, with one source neighborhood
and one lower bound for every index. -/
theorem exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ ψ ∈ V, ∀ n : ℤ,
          c ≤ (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re := by
  obtain ⟨V₀,hV₀open,hφV₀,F,hFapply,hFcont⟩ :=
    exists_local_sourceNormalizedActionDeviation_continuousMap
      hp hp1 hq1 hq hhalf φ hreal
  obtain ⟨K,hK⟩ := Coeff.exists_cutoff_norm_apply_lt hq (F φ)
    (by norm_num : (0:ℝ) < 1/4)
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let b (n : ℤ) : ℝ :=
    (4 * sourceNormalizedActionComplexExtension hp hp1 n φ).re
  have hbpos (n : ℤ) : 0 < b n := by
    have hpos := sourceNormalizedActionComplexExtension_re_pos_of_realType
      hp hp1 n φ hreal
    dsimp [b]
    simpa [Complex.mul_re] using
      (mul_pos (by norm_num : (0:ℝ) < 4) hpos)
  have hmin : ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧
      ∀ n ∈ s, c ≤ b n/2 := by
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨1/2,by norm_num,le_rfl,by simp⟩
    | @insert n t hn ih =>
        obtain ⟨c,hc,hchalf,hct⟩ := ih
        refine ⟨min c (b n/2),lt_min hc (half_pos (hbpos n)),
          (min_le_left _ _).trans hchalf,?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hkt
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hct k hkt)
  obtain ⟨c,hc,hchalf,hcs⟩ := hmin
  have hnearC : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ s, b n/2 <
        (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re := by
    rw [Finset.eventually_all]
    intro n hn
    have hcont : ContinuousAt
        (fun ψ : CoeffPair p =>
          (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re) φ := by
      have hd := differentiableAt_sourceNormalizedActionComplexExtension_of_realType
        hp hp1 φ hreal n
      exact continuous_re.continuousAt.comp (hd.const_mul 4).continuousAt
    have hhalf : b n/2 < b n := by linarith [hbpos n]
    have hnear : ∀ᶠ z : ℝ in 𝓝
        ((4 * sourceNormalizedActionComplexExtension hp hp1 n φ).re),
        b n/2 < z :=
      lt_mem_nhds (by simpa only [b] using hhalf)
    exact hcont.eventually hnear
  have hFcontAt : ContinuousAt F φ :=
    (hFcont φ hφV₀).continuousAt (hV₀open.mem_nhds hφV₀)
  have hnearF : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ‖F ψ-F φ‖ < 1/4 := by
    have he := hFcontAt.eventually
      (Metric.ball_mem_nhds (F φ) (by norm_num : (0:ℝ) < 1/4))
    filter_upwards [he] with ψ hψ
    simpa only [mem_ball,dist_eq_norm] using hψ
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp (hnearC.and hnearF)
  let V := V₀ ∩ U
  refine ⟨V,hV₀open.inter hUopen,⟨hφV₀,hφU⟩,c,hc,?_⟩
  intro ψ hψ n
  by_cases hn : K ≤ n.natAbs
  · have hbase : ‖F φ n‖ < 1/4 := hK n hn
    have hclose : ‖F ψ n-F φ n‖ < 1/4 := by
      have hpoint := lp.norm_apply_le_norm
        (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' (F ψ-F φ) n
      have hpoint' : ‖F ψ n-F φ n‖ ≤ ‖F ψ-F φ‖ := by
        simpa using hpoint
      exact hpoint'.trans_lt (hUsub hψ.2).2
    have htail : ‖sourceNormalizedActionDeviation hp hp1 ψ n‖ < 1/2 := by
      rw [← hFapply ψ hψ.1 n]
      have htri := norm_le_norm_sub_add (F ψ n) (F φ n)
      linarith
    have hreal := (abs_le.mp (Complex.abs_re_le_norm
      (sourceNormalizedActionDeviation hp hp1 ψ n))).1
    have hreEq :
        (sourceNormalizedActionDeviation hp hp1 ψ n).re =
          (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re - 1 := by
      simp [sourceNormalizedActionDeviation]
    linarith
  · have hns : n ∈ s := by
      simp only [s,Finset.mem_Icc]
      omega
    exact (hcs n hns).trans (((hUsub hψ.2).1 n hns).le)

/-- The principal square-root coordinates are all complex
differentiable and nonvanishing on one complex source neighborhood.
Their squares recover four times the normalized actions. -/
theorem exists_local_sourceNormalizedActionRoot_allCoordinates
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℝ, 0 < c ∧
        (∀ ψ ∈ V, ∀ n : ℤ,
          c ≤ (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re) ∧
        (∀ n : ℤ, DifferentiableOn ℂ
          (sourceNormalizedActionRoot hp hp1 n) V) ∧
        (∀ ψ ∈ V, ∀ n : ℤ,
          sourceNormalizedActionRoot hp hp1 n ψ ≠ 0 ∧
          (sourceNormalizedActionRoot hp hp1 n ψ)^2 =
            4 * sourceNormalizedActionComplexExtension hp hp1 n ψ) := by
  obtain ⟨Vp,hVpopen,hφVp,c,hc,hpos⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos
      hp hp1 hq1 hq hhalf φ hreal
  obtain ⟨Vd,hVdopen,hφVd,hdiff⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_differentiableOn
      hp hp1 φ hreal
  let V := Vp ∩ Vd
  have hVopen : IsOpen V := hVpopen.inter hVdopen
  have hVpos (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      0 < (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ).re :=
    hc.trans_le (hpos ψ hψ.1 n)
  refine ⟨V,hVopen,⟨hφVp,hφVd⟩,c,hc,
    (fun ψ hψ n => hpos ψ hψ.1 n),?_,?_⟩
  · intro n ψ hψ
    have hslit : 4 * sourceNormalizedActionComplexExtension hp hp1 n ψ ∈
        Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hVpos ψ hψ n))
    have hF : DifferentiableAt ℂ
        (sourceNormalizedActionComplexExtension hp hp1 n) ψ :=
      (hdiff n ψ hψ.2).differentiableAt (hVdopen.mem_nhds hψ.2)
    have hinner : DifferentiableAt ℂ
        (fun χ => 4 * sourceNormalizedActionComplexExtension hp hp1 n χ) ψ :=
      hF.const_mul 4
    exact ((Complex.differentiableAt_sqrt hslit).comp ψ
      hinner).differentiableWithinAt
  · intro ψ hψ n
    let z := 4 * sourceNormalizedActionComplexExtension hp hp1 n ψ
    have hz : z ≠ 0 := by
      intro he
      have hp0 := hVpos ψ hψ n
      change 0 < z.re at hp0
      rw [he] at hp0
      norm_num at hp0
    have hsq : (Complex.sqrt z)^2 = z := by
      have h := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
      norm_num at h
      simpa only [Complex.sqrt,one_div] using h
    constructor
    · intro he
      change Complex.sqrt z = 0 at he
      rw [he] at hsq
      exact hz (by simpa using hsq.symm)
    · exact hsq

end NLS.ZakharovShabat
