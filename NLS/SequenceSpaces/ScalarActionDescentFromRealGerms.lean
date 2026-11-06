import NLS.SequenceSpaces.LocalScalarActionDescent
import NLS.SequenceSpaces.NonzeroFiniteCenter
import NLS.SequenceSpaces.ComplexSignInvariance
import NLS.SequenceSpaces.ComplexActionStationarity
import NLS.SequenceSpaces.RealActionBallGluing
import NLS.SequenceSpaces.RealActionLifting

/-! # Global analytic action descent from actual real invariance and complex germs

A function on a real sequence space that is constant on complete quadratic
action fibers and has genuine complex analytic germs admits a complex
analytic action factor near the entire nonnegative action cone. Closed
gaps and arbitrary infinite support are included.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Real quadratic-action invariance supplies the tail sign and infinitesimal
rotation hypotheses for local analytic descent at every real base. -/
theorem exists_local_scalar_action_factor_of_real_invariance (hp : p ≠ ⊤)
    (f : (Coeff p × Coeff p) → ℂ) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hinv : ∀ z ∈ U, ∀ w ∈ U, z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → f w = f z)
    (z₀ : Coeff p × Coeff p) (hz₀ : z₀ ∈ U) (hr₀ : z₀ ∈ realPairLocus p) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ U ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧ ∀ z ∈ Z, g (quadraticActionsExponent z) = f z := by
  obtain ⟨S,R,hR,hbase,hball,hhead⟩ := exists_nonzeroFiniteCenter_ball hp U hU z₀ hz₀
  let c := truncatePair S z₀
  have hcr : c ∈ realPairLocus p := truncatePair_mem_realPairLocus S z₀ hr₀
  have hI : ∀ z ∈ ball c R, ∀ w ∈ ball c R,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → f w = f z :=
    fun z hz w hw => hinv z (hball hz) w (hball hw)
  have hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ ball c R, f (pairSignChange e d z) = f z := by
    intro e d he hd z hz
    exact eqOn_pairSignChange_of_real_action_invariance f c R hR hcr (hf.mono hball) hI
      e d (pairSignChange_truncatePair S z₀ e d he hd) hz
  have hrot : ∀ z ∈ ball c R, ∀ k, fderiv ℂ f z (actionRotationVectorCLM p k z) = 0 := by
    intro z hz k
    exact fderiv_actionRotationVector_eq_zero_of_real_action_invariance f _ isOpen_ball
      (convex_ball c R) c (mem_ball_self hR) hcr (hf.mono hball) hI z hz k
  obtain ⟨Z,T,g,hZ,hz,hsub,hT,himage,hg,hrec⟩ := exists_local_scalar_action_factor
    (q := q) hp S f (ball c R) isOpen_ball (hf.mono hball) hsign hrot z₀ hbase hhead
  exact ⟨Z,T,g,hZ,hz,hsub.trans hball,hT,himage,hg,hrec⟩

/-- Genuine complex germs and real action-fiber invariance give a globally
glued analytic factor near the WHOLE nonnegative action cone. -/
theorem exists_analytic_action_factor_of_real_germs (hp : p ≠ ⊤)
    (f : (Coeff p × Coeff p) → ℂ)
    (hinv : ∀ z w, z ∈ realPairLocus p → w ∈ realPairLocus p →
      quadraticActionsExponent (q := q) w = quadraticActionsExponent z → f w = f z)
    (hgerm : ∀ z ∈ realPairLocus p,
      ∃ U : Set (Coeff p × Coeff p), IsOpen U ∧ z ∈ U ∧
      ∃ F : (Coeff p × Coeff p) → ℂ, AnalyticOnNhd ℂ F U ∧
        ∀ y ∈ U, y ∈ realPairLocus p → F y = f y) :
    ∃ U : Set (Coeff q), ∃ g : Coeff q → ℂ,
      IsOpen U ∧ nonnegativeLocus q ⊆ U ∧ AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ realPairLocus p, g (quadraticActionsExponent z) = f z := by
  classical
  let A := {z : Coeff p × Coeff p // z ∈ realPairLocus p}
  let a : A → Coeff q := fun z => quadraticActionsExponent z.val
  have ha (z : A) : a z ∈ nonnegativeLocus q := quadraticActions_mem_nonnegativeLocus z.val z.property
  have hlocal (z : A) : ∃ r : ℝ, 0 < r ∧ ∃ g : Coeff q → ℂ,
      AnalyticOnNhd ℂ g (ball (a z) r) ∧ ∀ w : A, a w ∈ ball (a z) r → g (a w) = f w.val := by
    obtain ⟨V,hV,hz,F,hF,hmatch⟩ := hgerm z.val z.property
    have hI : ∀ v ∈ V, ∀ w ∈ V, v ∈ realPairLocus p → w ∈ realPairLocus p →
        (∀ n, w.1 n^2+w.2 n^2 = v.1 n^2+v.2 n^2) → F w = F v := by
      intro v hv w hw hvr hwr he
      rw [hmatch w hw hwr,hmatch v hv hvr]
      apply hinv v w hvr hwr
      ext n
      simp only [quadraticActionsExponent_apply,he n]
    obtain ⟨Z,T,g,hZ,hzZ,_hZV,hT,himage,hg,hrec⟩ :=
      exists_local_scalar_action_factor_of_real_invariance (q := q) hp F V hV hF hI z.val hz z.property
    have hzT : a z ∈ T := himage ▸ mem_image_of_mem _ hzZ
    obtain ⟨r₁,hr₁,hball⟩ := Metric.isOpen_iff.mp hT (a z) hzT
    obtain ⟨r₂,hr₂,hlift⟩ := exists_ball_real_quadraticActions_lifts (q := q) hp z.val z.property Z hZ hzZ
    refine ⟨min r₁ r₂,lt_min hr₁ hr₂,g,hg.mono (fun b hb => hball (ball_subset_ball (min_le_left _ _) hb)),?_⟩
    intro w hw
    obtain ⟨v,⟨hv,hvr⟩,he⟩ := hlift ⟨ball_subset_ball (min_le_right _ _) hw,ha w⟩
    have hvV : v ∈ V := _hZV hv
    rw [←he,hrec v hv,hmatch v hvV hvr]
    exact hinv w.val v w.property hvr he
  choose r hr g hg hrec using hlocal
  have hreal : ∀ z b, b ∈ ball (a z) (r z) → b ∈ nonnegativeLocus q → ∃ w : A, a w = b := by
    intro z b _ hb
    obtain ⟨w,hw,he⟩ := exists_real_quadraticActions_lift hp b hb
    exact ⟨⟨w,hw⟩,he.1⟩
  obtain ⟨G,hG,hrecover⟩ := exists_analytic_gluing_of_real_action_ball_recovery hp a r
    (fun z => f z.val) ha hr hreal (fun z => ⟨g z,hg z,hrec z⟩)
  refine ⟨⋃ z, ball (a z) (r z),G,isOpen_iUnion (fun _ => isOpen_ball),?_,hG,?_⟩
  · intro b hb
    obtain ⟨w,hw,he⟩ := exists_real_quadraticActions_lift hp b hb
    exact mem_iUnion.mpr ⟨⟨w,hw⟩,he.1 ▸ mem_ball_self (hr ⟨w,hw⟩)⟩
  · intro z hz
    exact hrecover ⟨z,hz⟩

end NLS.Coeff
