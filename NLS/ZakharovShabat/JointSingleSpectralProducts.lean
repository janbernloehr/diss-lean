import NLS.ZakharovShabat.SingleSpectralProductFamilies
import NLS.ZakharovShabat.RestoredSpectralPairs
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# Joint analyticity of the full single-root product

The normalized single-root products converge uniformly on compact spectral
sets over bounded sets of `ℓᵖ` root displacements. Their finite cutoffs are
analytic in both the spectral variable and the displacement sequence. This
gives a joint entire function, the numerator before deleting one index in
Corollary 10.6.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite normalized single-root product in joint coordinates. -/
def jointSingleSpectralPartialProduct (N : ℕ) : ℂ × Coeff p → ℂ :=
  fun t => singleSpectralPartialProduct (displacedRoots t.2) t.1 N

/-- The full single-root product in joint spectral/displacement coordinates. -/
def jointSingleSpectralProduct : ℂ × Coeff p → ℂ :=
  fun t => entireSingleSpectralProduct (displacedRoots t.2) t.1

/-- Each literal finite cutoff is jointly entire. -/
theorem analyticOnNhd_jointSingleSpectralPartialProduct (N : ℕ) :
    AnalyticOnNhd ℂ (jointSingleSpectralPartialProduct (p := p) N) Set.univ := by
  intro t _
  have hfactor (m : ℤ) : AnalyticAt ℂ
      (fun q : ℂ × Coeff p => singleSpectralFactor (displacedRoots q.2) q.1 m) t := by
    have hcoeff : AnalyticAt ℂ (fun a : Coeff p => a m) t.2 := by
      convert (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).analyticAt t.2 using 1
      funext a
      rfl
    have hroot : AnalyticAt ℂ (fun q : ℂ × Coeff p => displacedRoots q.2 m) t :=
      analyticAt_const.add (hcoeff.comp analyticAt_snd)
    exact (hroot.sub analyticAt_fst).div_const
  change AnalyticAt ℂ (fun q : ℂ × Coeff p =>
    2 * ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      singleSpectralFactor (displacedRoots q.2) q.1 m) t
  exact analyticAt_const.mul
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).analyticAt_fun_prod
      (fun m _ => hfactor m))

/-- On every compact spectral set and bounded displacement set, the literal
finite cutoffs converge uniformly to the actual single-root product. -/
theorem tendstoUniformlyOn_jointSingleSpectralProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (K : Set ℂ) (hK : IsCompact K) (S : Set (Coeff p))
    (R : ℝ) (hR : 0 ≤ R) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    TendstoUniformlyOn (jointSingleSpectralPartialProduct (p := p))
      (jointSingleSpectralProduct (p := p)) atTop (K ×ˢ S) := by
  change TendstoUniformlyOn
    (fun N (t : ℂ × Coeff p) => singleSpectralPartialProduct (displacedRoots t.2) t.1 N)
    (fun t => entireSingleSpectralProduct (displacedRoots t.2) t.1) atTop (K ×ˢ S)
  exact tendstoUniformlyOn_entireSingleSpectralProduct_family hp hp1
      (displacedRoots (p := p)) memℓp_displacedRoots S R hR
      (by intro a ha; simpa only [show (⟨_, memℓp_displacedRoots a⟩ : Coeff p) = a
        from by ext n; simp [displacedRoots]] using hb a ha) K hK

/-- The full infinite single-root product is jointly entire in its spectral
parameter and `ℓᵖ` displacement sequence. -/
theorem analyticOnNhd_jointSingleSpectralProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (jointSingleSpectralProduct (p := p)) Set.univ := by
  have huniform (t : ℂ × Coeff p) (_ : t ∈ (Set.univ : Set (ℂ × Coeff p))) :
      ∃ U : Set (ℂ × Coeff p), IsOpen U ∧ t ∈ U ∧
        TendstoUniformlyOn (jointSingleSpectralPartialProduct (p := p))
          (jointSingleSpectralProduct (p := p)) atTop U := by
    let K : Set ℂ := closedBall t.1 1
    let S : Set (Coeff p) := closedBall t.2 1
    let U : Set (ℂ × Coeff p) := ball t.1 1 ×ˢ ball t.2 1
    have hb : ∀ a ∈ S, ‖a‖ ≤ ‖t.2‖+1 := by
      intro a ha
      have hdist : ‖a-t.2‖ ≤ (1 : ℝ) := by
        have h := mem_closedBall.mp ha
        simpa only [dist_eq_norm] using h
      calc
        ‖a‖ = ‖(a-t.2)+t.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖a-t.2‖+‖t.2‖ := norm_add_le _ _
        _ ≤ ‖t.2‖+1 := by linarith
    refine ⟨U, isOpen_ball.prod isOpen_ball, ⟨mem_ball_self (by norm_num),
      mem_ball_self (by norm_num)⟩, ?_⟩
    exact (tendstoUniformlyOn_jointSingleSpectralProduct hp hp1 K
      (isCompact_closedBall _ _) S (‖t.2‖+1) (by positivity) hb).mono
      (fun q hq => ⟨mem_closedBall.mpr (le_of_lt hq.1),
        mem_closedBall.mpr (le_of_lt hq.2)⟩)
  have happrox := NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximationOn.of_open_local_uniform
    isOpen_univ (fun N => analyticOnNhd_jointSingleSpectralPartialProduct (p := p) N)
    huniform
  exact NLS.ComplexAnalysis.analyticOnNhd_of_complexSmoothOn _ isOpen_univ
    happrox.contDiffOn

end NLS.ZakharovShabat
