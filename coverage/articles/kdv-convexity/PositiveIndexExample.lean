import NLS.Articles.KdVConvexity.LocalConsequences

set_option autoImplicit false
open Set

/-- Check the inverse adapter directly on the paper's positive-index ell2. -/
example {F : lp (fun _ : ℕ+ => ℂ) 2 → lp (fun _ : ℕ+ => ℂ) 2}
    {U : Set (lp (fun _ : ℕ+ => ℂ) 2)}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    (h0 : (0 : lp (fun _ : ℕ+ => ℂ) 2) ∈ U) (hF0 : F 0 = 0)
    (hd : fderiv ℂ F 0 = (-6 : ℂ) • ContinuousLinearMap.id ℂ _) :
    ∃ V W, IsOpen V ∧ IsOpen W ∧ (0 : lp (fun _ : ℕ+ => ℂ) 2) ∈ V ∧
      (0 : lp (fun _ : ℕ+ => ℂ) 2) ∈ W ∧ V ⊆ U ∧
      F '' V = W ∧ Set.BijOn F V W ∧
      ∃ G, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ G W ∧
        (∀ b ∈ V, G (F b) = b) ∧ (∀ c ∈ W, G c ∈ V ∧ F (G c) = c) :=
  NLS.Articles.KdVConvexity.local_open_inverse_of_derivative_neg_six hU hF h0 hF0 hd
