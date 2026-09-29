import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Analytic inverse branches on a quantitative common ball

A joint derivative Lipschitz bound and a bound for the base derivative
inverse give explicit source and image radii. Pointwise invertibility
on the larger domain makes the resulting inverse analytic throughout
the smaller image ball.
-/

noncomputable section
open Set Filter Topology Metric
open scoped NNReal
namespace NLS.ComplexAnalysis

def quantitativeInverseJointRadius (R B L : ℝ) : ℝ :=
  min (R/2) (1/(4*B*(L+1)))

def quantitativeInverseImageRadius (R B L : ℝ) : ℝ :=
  quantitativeInverseJointRadius R B L/(8*B)

theorem quantitativeInverseJointRadius_pos {R B L : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hL : 0 ≤ L) :
    0 < quantitativeInverseJointRadius R B L := by
  unfold quantitativeInverseJointRadius
  positivity

theorem quantitativeInverseImageRadius_pos {R B L : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hL : 0 ≤ L) :
    0 < quantitativeInverseImageRadius R B L :=
  div_pos (quantitativeInverseJointRadius_pos hR hB hL) (by positivity)

theorem exists_analytic_inverse_on_uniform_ball
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X]
    (f : X → X) (a : X) (R B L : ℝ)
    (hR : 0 < R) (hB : 1 ≤ B) (hL : 0 ≤ L)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (T : X ≃L[ℂ] X) (hT : (T : X →L[ℂ] X) = fderiv ℂ f a)
    (hTB : ‖(T.symm : X →L[ℂ] X)‖ ≤ B)
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x-fderiv ℂ f y‖ ≤ L*‖x-y‖)
    (hbij : ∀ x ∈ ball a R, Function.Bijective (fderiv ℂ f x)) :
    ∃ g : X → X,
      AnalyticOnNhd ℂ g (ball (f a) (quantitativeInverseImageRadius R B L)) ∧
      g (f a) = a ∧
      ∀ y ∈ ball (f a) (quantitativeInverseImageRadius R B L),
        g y ∈ ball a (quantitativeInverseJointRadius R B L) ∧ f (g y) = y ∧
        ∀ x ∈ ball a (quantitativeInverseJointRadius R B L), f x = y → x = g y := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · have : Subsingleton X := hX
    refine ⟨fun _ => a,(fun _ _ => analyticAt_const),rfl,?_⟩
    intro y hy
    exact ⟨mem_ball_self (quantitativeInverseJointRadius_pos hR
      (lt_of_lt_of_le zero_lt_one hB) hL),Subsingleton.elim _ _,
      fun x _ _ => Subsingleton.elim x a⟩
  have : Nontrivial X := hX
  let ρ := quantitativeInverseJointRadius R B L
  let δ := quantitativeInverseImageRadius R B L
  let N := ‖(T.symm : X →L[ℂ] X)‖
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hρ : 0 < ρ := quantitativeInverseJointRadius_pos hR hBpos hL
  have hδ : 0 < δ := quantitativeInverseImageRadius_pos hR hBpos hL
  have hρR : ρ < R := (min_le_left _ _).trans_lt (by linarith)
  have hρq : ρ ≤ 1/(4*B*(L+1)) := min_le_right _ _
  have hsub : ball a ρ ⊆ ball a R := ball_subset_ball hρR.le
  let c : ℝ≥0 := ⟨1/(2*B),by positivity⟩
  have hsmall : L*ρ ≤ (c:ℝ) := by
    have hden : 0 < 4*B*(L+1) := by positivity
    have hprod := (le_div_iff₀ hden).mp hρq
    change L*ρ ≤ 1/(2*B)
    apply (le_div_iff₀ (by positivity : 0 < 2*B)).mpr
    nlinarith [mul_nonneg hBpos.le (mul_nonneg hL hρ.le)]
  have hN : 0 < N := ContinuousLinearEquiv.norm_pos T.symm
  have hinv : 1/B ≤ N⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hN hTB
  have hcReal : (c:ℝ) < N⁻¹ := by
    have h : 1/(2*B) < 1/B := one_div_lt_one_div_of_lt hBpos (by linarith)
    exact h.trans_le hinv
  have hc : c < ‖(T.symm : X →L[ℂ] X)‖₊⁻¹ := by
    exact_mod_cast hcReal
  have happrox : ApproximatesLinearOn f (T : X →L[ℂ] X) (ball a ρ) c := by
    let k : X → X := fun x => f x-T x
    have hk (x : X) (hx : x ∈ ball a ρ) : DifferentiableAt ℂ k x :=
      (hf x (hsub hx)).differentiableAt.sub T.differentiableAt
    have hkBound (x : X) (hx : x ∈ ball a ρ) : ‖fderiv ℂ k x‖ ≤ (c:ℝ) := by
      have hder : fderiv ℂ k x = fderiv ℂ f x-(T : X →L[ℂ] X) := by
        exact ((hf x (hsub hx)).differentiableAt.hasFDerivAt.sub T.hasFDerivAt).fderiv
      rw [hder,hT]
      exact (hLip x (hsub hx) a (mem_ball_self hR)).trans
        ((mul_le_mul_of_nonneg_left (le_of_lt (by
          simpa only [mem_ball,dist_eq_norm] using hx)) hL).trans hsmall)
    have hklip : LipschitzOnWith c k (ball a ρ) :=
      (convex_ball a ρ).lipschitzOnWith_of_nnnorm_fderiv_le hk
        (fun x hx => by exact_mod_cast hkBound x hx)
    exact hklip.approximatesLinearOn
  let P := happrox.toOpenPartialHomeomorph f (ball a ρ) (Or.inr hc) isOpen_ball
  have hPeq : (P : X → X) = f :=
    ApproximatesLinearOn.toOpenPartialHomeomorph_coe f (ball a ρ) happrox (Or.inr hc) isOpen_ball
  have hsource : P.source = ball a ρ :=
    ApproximatesLinearOn.toOpenPartialHomeomorph_source f (ball a ρ) happrox (Or.inr hc) isOpen_ball
  have htarget := happrox.closedBall_subset_target (Or.inr hc) isOpen_ball
    (by positivity : 0 ≤ ρ/2) (closedBall_subset_ball (by linarith : ρ/2 < ρ))
  have hδbound : δ ≤ ((‖(T.symm : X →L[ℂ] X)‖₊⁻¹ : ℝ)-(c:ℝ))*(ρ/2) := by
    change ρ/(8*B) ≤ (N⁻¹-1/(2*B))*(ρ/2)
    calc
      _ ≤ (1/B-1/(2*B))*(ρ/2) := by
        field_simp
        nlinarith
      _ ≤ (N⁻¹-1/(2*B))*(ρ/2) := mul_le_mul_of_nonneg_right
        (sub_le_sub_right hinv _) (by positivity)
  have hmem (y : X) (hy : y ∈ ball (f a) δ) : y ∈ P.target :=
    htarget ((closedBall_subset_closedBall hδbound) (ball_subset_closedBall hy))
  let g : X → X := P.symm
  have hgsource (y : X) (hy : y ∈ ball (f a) δ) : g y ∈ P.source :=
    P.symm.mapsTo (hmem y hy)
  have hright (y : X) (hy : y ∈ ball (f a) δ) : f (g y) = y := by
    rw [← hPeq]
    exact P.right_inv (hmem y hy)
  have hga : g (f a) = a := by
    rw [← hPeq]
    exact P.left_inv (by rw [hsource]; exact mem_ball_self hρ)
  refine ⟨g,?_,hga,?_⟩
  · intro y hy
    have hx : g y ∈ ball a R := hsub (by rw [← hsource]; exact hgsource y hy)
    let j := ContinuousLinearEquiv.ofBijective (fderiv ℂ f (g y))
      (LinearMap.ker_eq_bot.mpr (hbij (g y) hx).1)
      (LinearMap.range_eq_top.mpr (hbij (g y) hx).2)
    have hj : HasFDerivAt f (j : X →L[ℂ] X) (g y) := by
      simpa only [j,ContinuousLinearEquiv.coe_ofBijective] using (hf (g y) hx).differentiableAt.hasFDerivAt
    have hAna : AnalyticAt ℂ P.symm (P (g y)) := by
      apply P.analyticAt_symm' (i := j) (hgsource y hy)
      · rw [hPeq]; exact hf (g y) hx
      · rw [hPeq]; exact hj.fderiv
    rw [hPeq,hright y hy] at hAna
    exact hAna
  · intro y hy
    refine ⟨by rw [← hsource]; exact hgsource y hy,hright y hy,?_⟩
    intro x hx hxy
    calc
      x = P.symm (P x) := (P.left_inv (by rw [hsource]; exact hx)).symm
      _ = g y := by rw [hPeq,hxy]

end NLS.ComplexAnalysis
