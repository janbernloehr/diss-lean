import NLS.KdV.HillDirichletAnalyticAngles
import NLS.KdV.HillRegularAngleCompatibility

/-! # Original sheeted Dirichlet terminals and choice-independent regular Abelian terms

The terminal is selected from the original Hill energy and logarithmic
Dirichlet multiplier. Period normalization removes the ambiguity of a
real lift. A closed gap contributes zero to the regular correction.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def hillSelectedDirichletAngle (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k ≠ 0) : ℝ :=
  (Classical.choose (exists_hillDirichlet_terminal_angle q.val q.property.1 q.property.2 k hk hgap)).re

theorem hillSelectedDirichletAngle_spec (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1 ≤ k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k ≠ 0) :
    let θ := hillSelectedDirichletAngle q k hk hgap
    θ ∈ Icc (-Real.pi) Real.pi ∧
      cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
        (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ) =
          (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) ∧
      cos (θ : ℂ) = hillDirichletGapCosine q.val q.property.1 q.property.2 k hk ∧
      sin (θ : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 k hk := by
  let e := Classical.choose (exists_hillDirichlet_terminal_angle q.val q.property.1 q.property.2 k hk hgap)
  have he := Classical.choose_spec (exists_hillDirichlet_terminal_angle q.val q.property.1 q.property.2 k hk hgap)
  have hi : e.im = 0 := im_eq_zero_of_mem_real_segment (-Real.pi) Real.pi e (by simpa only [ofReal_neg] using he.1)
  have hr : e = (e.re : ℂ) := by apply Complex.ext <;> simp only [ofReal_re,ofReal_im,hi]
  have hb : e.re ∈ Icc (-Real.pi) Real.pi :=
    re_mem_Icc_of_mem_real_segment (-Real.pi) Real.pi (by linarith [Real.pi_pos]) e
      (by simpa only [ofReal_neg] using he.1)
  change e.re ∈ Icc (-Real.pi) Real.pi ∧ _
  have hp : cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 k) e =
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ) := he.2.1
  have hcos : cos e = hillDirichletGapCosine q.val q.property.1 q.property.2 k hk := he.2.2.1
  have hsin : sin e = hillDirichletGapSine q.val q.property.1 q.property.2 k hk := he.2.2.2
  rw [hr] at hp hcos hsin
  exact ⟨hb,hp,hcos,hsin⟩

def hillDirichletRegularAbelianTerm (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) : ℂ :=
  if hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k = 0 then 0 else
    hillRegularAbelianPrimitive q.val q.property.1 q.property.2 n hn k
      (hillSelectedDirichletAngle q k hk hgap : ℂ)

theorem hillDirichletRegularAbelianTerm_closed (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k = 0) :
    hillDirichletRegularAbelianTerm q n hn k hk = 0 := by
  rw [hillDirichletRegularAbelianTerm,dif_pos hgap]

theorem hillDirichletRegularAbelianTerm_eq_terminal (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k ≠ 0)
    (θ : ℝ)
    (hp : cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
      (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ) =
        (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (hs : sin (θ : ℂ) = hillDirichletGapSine q.val q.property.1 q.property.2 k hk) :
    hillDirichletRegularAbelianTerm q n hn k hk =
      hillRegularAbelianPrimitive q.val q.property.1 q.property.2 n hn k (θ : ℂ) := by
  rw [hillDirichletRegularAbelianTerm,dif_neg hgap]
  have he := hillSelectedDirichletAngle_spec q k hk hgap
  exact hillRegularAbelianPrimitive_terminal_independent q.val q.property.1 q.property.2 n k hn hk hgap
    _ θ he.2.1 hp he.2.2.2 hs

theorem hillDirichletRegularAbelianTerm_im_eq_zero (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : 1 ≤ k) : (hillDirichletRegularAbelianTerm q n hn k hk).im = 0 := by
  unfold hillDirichletRegularAbelianTerm
  split_ifs
  · rfl
  · exact hillRegularAbelianPrimitive_im_eq_zero q.val q.property.1 q.property.2 n hn k hk _

end NLS.KdV
