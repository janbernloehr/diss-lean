import NLS.ZakharovShabat.SourceNormalizedActionFactorCommonExponentDomain
import NLS.ZakharovShabat.SourceNormalizedActionComplexUniformSequenceMajorants
import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceSpace

/-!
# A common source domain for normalized-action tail exponents

The deleted factor has all finite `ℓq` majorants on one neighborhood
when `1 < p ≤ 2`. The fixed-circle correction only needs one bounded
factor estimate, which can be taken at `q = 2`. Thus the action tail
majorants also share a source neighborhood and tail cutoff.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `1 < p ≤ 2`, the common-circle normalized-action candidate
has `ℓq + ℓ^(p/2)` tail majorants on one source neighborhood for
every finite `q > 1`. For each `q`, their norms are bounded uniformly
over the source neighborhood. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ,
        ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
          ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
            ∃ Cq : Coeff q,
              ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
                (∀ n : ℤ, K ≤ n.natAbs →
                  ‖4 * sourceNormalizedActionCircleCandidate hp hp1 n
                      ((Real.pi:ℂ)*n) (Real.pi/8) ψ - 1‖ ≤
                    ‖Cq n‖ + ‖Cg n‖) ∧
                ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vf,hVfopen,hφVf,Kf,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_disc_allExponents
      hp hp1 hp2 φ hφ
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcircle⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circles hp hp1 φ
  obtain ⟨Vs,hVsopen,hφVs,R,hR,hS⟩ :=
    exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  have hhalf2 : ENNReal.ofReal (p.toReal/2) ≤ (2 : ℝ≥0∞) :=
    (source_half_le_one hp hp2).trans (by norm_num)
  obtain ⟨Vd,hVdopen,hφVd,Kd,C,hC,hcorr⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_correction
      (q := 2) hp hp1 (by norm_num) (by norm_num) hhalf2 φ hφ
  let V := ((Vf ∩ Vc) ∩ Vs) ∩ Vd
  let K := max Kf (max Kc Kd)
  let r := ENNReal.ofReal (p.toReal/2)
  let Ls : ℝ := 4*C*R^2
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hrEq : r.toReal = p.toReal/2 := by
    simp only [r, ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
  have hr : 0 < r.toReal := by rw [hrEq]; positivity
  have hrENN : 0 < r := ENNReal.ofReal_pos.mpr (by positivity)
  refine ⟨V,(((hVfopen.inter hVcopen).inter hVsopen).inter hVdopen),
    ⟨⟨⟨hφVf,hφVc⟩,hφVs⟩,hφVd⟩,K,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨Lq,Lfg,hfactorq⟩ := hfactor q hq1 hq
  let Lg : ℝ := max (Lfg+Ls)
    ((Lfg^r.toReal+Ls^r.toReal)^(r.toReal)⁻¹)
  refine ⟨Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactorq ψ hψ.1.1.1
  let S := sourcePeriodicSquaredGapCoeff hp hp1 ψ
  let Cq : Coeff q := Bq
  let G₁ : Coeff r := (1:ℂ) • Coeff.magnitude Bg
  let G₂ : Coeff r := ((4*C:ℝ):ℂ) • Coeff.magnitude S
  let Cg : Coeff r := G₁ + G₂
  have hG₁ : ‖G₁‖ ≤ Lfg := by
    simpa only [G₁, one_smul, Coeff.norm_magnitude_quasi hrENN.ne'] using hBg
  have hG₂ : ‖G₂‖ ≤ Ls := by
    have hn : ‖G₂‖ = 4*C*‖S‖ := by
      have h4C : 0 ≤ 4*C := by positivity
      change ‖(((4*C:ℝ):ℂ) • Coeff.magnitude S)‖ = 4*C*‖S‖
      rw [lp.norm_const_smul hrENN.ne', Coeff.norm_magnitude_quasi hrENN.ne']
      simp only [Complex.norm_real, Real.norm_of_nonneg h4C]
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hS ψ hψ.1.2) (by positivity)
  have hCg : ‖Cg‖ ≤ Lg :=
    Coeff.norm_add_le_uniform hr G₁ G₂ hG₁ hG₂
  refine ⟨Cq,Cg,?_,hBq,hCg⟩
  intro n hn
  have hKf : Kf ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKc : Kc ≤ n.natAbs :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hKd : Kd ≤ n.natAbs :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hseg,hdisc,_,_⟩ := hcircle ψ hψ.1.1.2 n hKc
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let E := sourceCriticalRootRatioExtension hp hp1 n ψ
  let A := sourceNormalizedActionCircleCandidate hp hp1 n
    ((Real.pi:ℂ)*n) (Real.pi/8) ψ
  have hτball : τ ∈ ball ((Real.pi:ℂ)*n) (Real.pi/8) :=
    hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hτdisc : τ ∈ refinedResonantDisk n :=
    hdisc (mem_closedBall.mpr (mem_ball.mp hτball).le)
  have hmid : ‖I*E τ - 1‖ ≤ ‖Bq n‖+‖Bg n‖ :=
    hpoint n hKf τ hτdisc
  have hcor : ‖A-I*E τ/4‖ ≤ C*‖S n‖ := by
    simpa only [A,E,τ,S,sourcePeriodicSquaredGapCoeff_apply] using
      hcorr ψ hψ.2 n hKd
  have hCgpoint : ‖Cg n‖ = ‖Bg n‖+4*C*‖S n‖ := by
    have h := norm_add_smul_magnitude_apply Bg S 1 (4*C)
      (by norm_num) (by positivity) n
    simpa only [Cg,G₁,G₂,Complex.ofReal_one,one_smul,one_mul] using h
  have heq : 4*A-1 = 4*(A-I*E τ/4)+(I*E τ-1) := by ring
  change ‖4*A-1‖ ≤ ‖Cq n‖+‖Cg n‖
  rw [heq]
  calc
    ‖4*(A-I*E τ/4)+(I*E τ-1)‖ ≤
        ‖4*(A-I*E τ/4)‖+‖I*E τ-1‖ := norm_add_le _ _
    _ = 4*‖A-I*E τ/4‖+‖I*E τ-1‖ := by simp
    _ ≤ 4*C*‖S n‖ + (‖Bq n‖+‖Bg n‖) := by
      have hcor' := mul_le_mul_of_nonneg_left hcor (by norm_num : (0:ℝ) ≤ 4)
      nlinarith [hmid]
    _ = ‖Cq n‖+‖Cg n‖ := by rw [hCgpoint]; dsimp [Cq]; ring

/-- The chart-independent complex normalized action inherits the
same common neighborhood and cutoff after the fixed-circle formula
is identified with its complex extension. -/
theorem exists_local_sourceNormalizedActionComplexExtension_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ,
        ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
          ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
            ∃ Cq : Coeff q,
              ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
                (∀ n : ℤ, K ≤ n.natAbs →
                  ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
                    ‖Cq n‖ + ‖Cg n‖) ∧
                ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vm,hVmopen,hφVm,Km,hmajor⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_allExponents
      hp hp1 hp2 φ hφ
  obtain ⟨Ka,r,hr,hagree⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_complex_agreement
      hp hp1 φ hφ
  let V := Vm ∩ ball φ r
  let K := max Km Ka
  refine ⟨V,hVmopen.inter Metric.isOpen_ball,
    ⟨hφVm,mem_ball_self hr⟩,K,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨Lq,Lg,hmajorq⟩ := hmajor q hq1 hq
  refine ⟨Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,hCq,hCg⟩ := hmajorq ψ hψ.1
  refine ⟨Cq,Cg,?_,hCq,hCg⟩
  intro n hn
  have hKm : Km ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKa : Ka ≤ n.natAbs := le_trans (le_max_right _ _) hn
  have heq := (hagree ψ hψ.2 n hKa).1
  rw [← heq]
  exact hpoint n hKm

/-- For `1 < p ≤ 2`, the full normalized-action deviation belongs to
every finite `ℓq`, `q > 1`, on one complex source neighborhood. Its
`ℓq` norm is locally bounded there for each target exponent. -/
theorem exists_local_sourceNormalizedActionDeviation_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
        ∃ M : ℝ, ∀ ψ ∈ V,
          ∃ A : Coeff q,
            (∀ n : ℤ, A n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
            ‖A‖ ≤ M := by
  obtain ⟨V₀,hV₀open,hφV₀,K,hmajor⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allExponents
      hp hp1 hp2 φ hφ
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let a (ψ : CoeffPair p) (n : ℤ) :=
    sourceNormalizedActionDeviation hp hp1 ψ n
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ s, ‖a ψ n‖ ≤ ‖a φ n‖+1 := by
    rw [Finset.eventually_all]
    intro n hn
    have hdiff := differentiableAt_sourceNormalizedActionComplexExtension_of_realType
      hp hp1 φ hφ n
    have hcont : ContinuousAt (fun ψ : CoeffPair p => ‖a ψ n‖) φ := by
      have hda : DifferentiableAt ℂ (fun ψ : CoeffPair p => a ψ n) φ := by
        change DifferentiableAt ℂ (fun ψ : CoeffPair p =>
          4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1) φ
        exact (hdiff.const_mul 4).sub_const 1
      exact hda.continuousAt.norm
    have hlt : ‖a φ n‖ < ‖a φ n‖+1 := by linarith
    filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with ψ hψ
    exact hψ.le
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  let V := V₀ ∩ U
  let B : ℝ := ∑ n ∈ s, (‖a φ n‖+1)
  refine ⟨V,hV₀open.inter hUopen,⟨hφV₀,hφU⟩,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨Lq,Lg,hmajorq⟩ := hmajor q hq1 hq
  let M : ℝ := s.card*B+(Lq+Lg)
  refine ⟨M,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,hCq,hCg⟩ := hmajorq ψ hψ.1
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hr : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (half_pos hpr)
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ q :=
    (source_half_le_one hp hp2).trans hq1.le
  obtain ⟨T,hTapply,hTnorm,hmem⟩ :=
    Coeff.exists_tailCoeff_of_twoSequenceMajorants
      hr hq1 hq hhalf (a ψ) K Cq Cg (by
        intro n hn
        exact hpoint n hn)
  let A : Coeff q := ⟨a ψ,hmem⟩
  have hcenter (n : ℤ) (hn : n ∈ s) : ‖A n‖ ≤ B := by
    calc
      ‖A n‖ = ‖a ψ n‖ := rfl
      _ ≤ ‖a φ n‖+1 := hUsub hψ.2 n hn
      _ ≤ B := Finset.single_le_sum (f := fun k => ‖a φ k‖+1)
        (fun k _ => by positivity) hn
  have hout (n : ℤ) (hn : n ∉ s) : A n = T n := by
    have hKn : K ≤ n.natAbs := by
      simp only [s,Finset.mem_Icc] at hn
      omega
    rw [hTapply n,if_pos hKn]
  refine ⟨A,fun n => rfl,?_⟩
  exact (Coeff.norm_le_of_eq_outside_finset A T s B hcenter hout).trans
    (add_le_add_right (hTnorm.trans (add_le_add hCq hCg)) _)

end NLS.ZakharovShabat
