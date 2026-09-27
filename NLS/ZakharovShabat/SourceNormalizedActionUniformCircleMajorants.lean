import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleCorrection
import NLS.ZakharovShabat.SourceSquaredGapNorm

/-!
# Complex sequence majorants for the common-circle candidate

The deleted-factor estimate applies at the moving periodic midpoint,
which stays inside the distant isolating disc. The uniform circle
correction is bounded by the squared gap. Together these give the
`ℓq + ℓ^(p/2)` asymptotic majorants for the fixed free-centered
contour candidate on one complex source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized-action candidate on common distant circles has
locally uniform `ℓq + ℓ^(p/2)` majorants at every nearby complex
source, without a noncollapsed-gap assumption. -/
theorem exists_local_sourceNormalizedAction_uniform_circle_sequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs →
            ‖4 * sourceNormalizedActionCircleCandidate hp hp1 n
                ((Real.pi:ℂ)*n) (Real.pi/8) ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖) ∧
          ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vf,hVfopen,hφVf,Kf,Lq,Lfg,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_disc_uniformMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcircle⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circles hp hp1 φ
  obtain ⟨Vs,hVsopen,hφVs,R,hR,hS⟩ :=
    exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  obtain ⟨Vd,hVdopen,hφVd,Kd,C,hC,hcorr⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_correction
      hp hp1 hq1 hq hhalf φ hφ
  let V := ((Vf ∩ Vc) ∩ Vs) ∩ Vd
  let K := max Kf (max Kc Kd)
  let r := ENNReal.ofReal (p.toReal/2)
  let Ls : ℝ := 4*C*R^2
  let Lg : ℝ := max (Lfg+Ls)
    ((Lfg^r.toReal+Ls^r.toReal)^(r.toReal)⁻¹)
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hrEq : r.toReal = p.toReal/2 := by
    simp only [r, ENNReal.toReal_ofReal (by positivity : 0 ≤ p.toReal/2)]
  have hr : 0 < r.toReal := by rw [hrEq]; positivity
  have hrENN : 0 < r := ENNReal.ofReal_pos.mpr (by positivity)
  refine ⟨V,(((hVfopen.inter hVcopen).inter hVsopen).inter hVdopen),
    ⟨⟨⟨hφVf,hφVc⟩,hφVs⟩,hφVd⟩,K,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactor ψ hψ.1.1.1
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

end NLS.ZakharovShabat
