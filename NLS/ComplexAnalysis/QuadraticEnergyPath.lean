import NLS.ComplexAnalysis.HolomorphicPathPullback

/-! Quadratic energy transport along actual endpoint paths. Equality
and integrability only need the open parameter interval, so integrable
singular endpoints are retained. Negating a path retains its orientation
in parameter time and contributes its exact derivative minus one. -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- The literal energy path, with both actual endpoints transported. -/
def quadraticEnergyPath {a b : ℂ} (c : ℂ) (γ : Path a b) : Path (a^2-c) (b^2-c) :=
  γ.map (show Continuous (fun z : ℂ => z^2-c) by fun_prop)

theorem quadraticEnergyPath_integral_and_integrability {a b : ℂ}
    (c : ℂ) (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (f g : ℂ → ℂ)
    (hpull : ∀ t∈Ioo (0:ℝ) 1,
      f ((γ.extend t)^2-c)*(2*γ.extend t)=g (γ.extend t)) :
    (CurveIntegrable (holomorphicOneForm f) (quadraticEnergyPath c γ) ↔
      CurveIntegrable (holomorphicOneForm g) γ) ∧
    (∫ᶜ z in quadraticEnergyPath c γ, holomorphicOneForm f z)=
      ∫ᶜ z in γ, holomorphicOneForm g z := by
  exact holomorphicPathPullback_integral_and_integrability f g (fun z => z^2-c)
    (fun z => 2*z) (by fun_prop) γ hγ
    (fun t _ => by simpa using ((hasDerivAt_id (γ.extend t)).pow 2).sub_const c) hpull

/-- An odd frequency numerator over an even prescribed sheet transports
to the SUM of the two actual signed-frequency path integrals. No endpoint
term or extra factor two is introduced. -/
theorem quadraticEnergyPath_integral_eq_signed_pair {a b : ℂ}
    (c : ℂ) (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (f g : ℂ → ℂ)
    (hpull : ∀ t∈Ioo (0:ℝ) 1, f ((γ.extend t)^2-c)*(2*γ.extend t)=
      g (γ.extend t)-g (-γ.extend t))
    (hpos : CurveIntegrable (holomorphicOneForm g) γ)
    (hneg : CurveIntegrable (holomorphicOneForm g) (γ.map continuous_neg)) :
    CurveIntegrable (holomorphicOneForm f) (quadraticEnergyPath c γ) ∧
      (∫ᶜ z in quadraticEnergyPath c γ, holomorphicOneForm f z)=
        (∫ᶜ z in γ, holomorphicOneForm g z)+
          ∫ᶜ z in γ.map continuous_neg, holomorphicOneForm g z := by
  have hn := holomorphicPathPullback_integral_and_integrability g (fun z => -g (-z))
    (fun z => -z) (fun _ => -1) continuous_neg γ hγ
    (fun t _ => (hasDerivAt_id (γ.extend t)).neg)
    (fun t _ => by ring)
  have hformneg : holomorphicOneForm (fun z => -g (-z)) =
      -holomorphicOneForm (fun z => g (-z)) := by
    ext z
    simp only [Pi.neg_apply,neg_apply,holomorphicOneForm_apply]
    ring
  have hminus : CurveIntegrable (holomorphicOneForm (fun z => g (-z))) γ := by
    have h := hn.1.mp hneg
    rw [hformneg] at h
    exact curveIntegrable_neg_iff.mp h
  have hsub : holomorphicOneForm (fun z => g z-g (-z)) =
      holomorphicOneForm g-holomorphicOneForm (fun z => g (-z)) := by
    ext z
    simp only [Pi.sub_apply,sub_apply,holomorphicOneForm_apply]
    ring
  have h := quadraticEnergyPath_integral_and_integrability c γ hγ f
    (fun z => g z-g (-z)) hpull
  refine ⟨h.1.mpr (hsub ▸ hpos.sub hminus),?_⟩
  rw [h.2,hsub,curveIntegral_sub hpos hminus]
  have he := hn.2
  rw [hformneg,curveIntegral_neg] at he
  rw [he]
  ring

end NLS.ComplexAnalysis
