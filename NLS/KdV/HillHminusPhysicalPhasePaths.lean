import NLS.KdV.HillHminusPrescribedPhasePullback

/-! Exact actual endpoint-path transport for the original physical
normalized numerator. All source neighborhoods precede every index,
sheet prescription and path. Integrability is retained at singular
endpoints; no equality of a replacement phase is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- The actual energy-path integral is the SUM of the two actual
source integrals along the positive and negated frequency paths.
The basepoints, orientations and two-z Jacobian are literal. -/
theorem exists_common_prescribed_path_pullback (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.source ∧
      ∀ a∈U, ∀ n : ℕ+, ∀ w A B : ℂ, ∀ γ : Path A B,
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand ((n:ℕ):ℤ)
          P.family.roots (sourceAngularRootSheet (by simp) w) (z,P.dirichletSource a))) γ →
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand ((n:ℕ):ℤ)
          P.family.roots (sourceAngularRootSheet (by simp) w) (z,P.dirichletSource a)))
          (γ.map continuous_neg) →
        CurveIntegrable (holomorphicOneForm (fun E => P.prescribedDifferential n w (E,a)))
          (quadraticEnergyPath P.miura.energyShift γ) ∧
        (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ,
          holomorphicOneForm (fun E => P.prescribedDifferential n w (E,a)) E)=
          sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
            (P.dirichletSource a) γ+
          sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
            (P.dirichletSource a) (γ.map continuous_neg) := by
  obtain ⟨U,hU,hqU,hUP,hpull⟩ := P.exists_common_prescribedDifferential_sourcePhase q hq hreal
  refine ⟨U,hU,hqU,hUP,?_⟩
  intro a ha n w A B γ hγ hpos hneg
  exact quadraticEnergyPath_integral_eq_signed_pair P.miura.energyShift γ hγ
    (fun E => P.prescribedDifferential n w (E,a))
    (fun z => sourceAngularIntegrand ((n:ℕ):ℤ) P.family.roots
      (sourceAngularRootSheet (by simp) w) (z,P.dirichletSource a))
    (fun t _ => hpull a ha n w (γ.extend t)) hpos hneg

end HillHminusPsiChart

/-- At EVERY original real source there is ONE original real
neighborhood on which EVERY fixed physical normalized energy integral
is exactly the sum of its two actual source-frequency path integrals.
This is the ORIGINAL physical numerator and radicand prescription. -/
theorem exists_hillOriginal_physical_phase_path_pullback (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, ∃ W : Set RealPeriodOneHillPotential,
      0<c ∧ M<c ∧ P.miura.energyShift=(c:ℂ)^2 ∧ IsOpen W ∧ q∈W ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots ∧
      ∀ p∈W, ∀ n : ℕ+, ∀ w A B : ℂ, ∀ γ : Path A B,
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) →
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand ((n:ℕ):ℤ)
          P.family.roots (sourceAngularRootSheet (by simp) w)
            (z,P.dirichletSource (hillOriginalHminusSource p.val)))) γ →
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand ((n:ℕ):ℤ)
          P.family.roots (sourceAngularRootSheet (by simp) w)
            (z,P.dirichletSource (hillOriginalHminusSource p.val)))) (γ.map continuous_neg) →
        let f := fun E : ℂ => hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos E/
          prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff p.val)) w E
        CurveIntegrable (holomorphicOneForm f) (quadraticEnergyPath P.miura.energyShift γ) ∧
          (∫ᶜ E in quadraticEnergyPath P.miura.energyShift γ, holomorphicOneForm f E)=
            sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
              (P.dirichletSource (hillOriginalHminusSource p.val)) γ+
            sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w)
              (P.dirichletSource (hillOriginalHminusSource p.val)) (γ.map continuous_neg) := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,H⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) M
  obtain ⟨U,hU,hqU,hUP,hpull⟩ := P.exists_common_prescribed_path_pullback
    (hillOriginalHminusSource q.val) hqP
    (hreal _ hqP.1 (hillOriginalHminusSource_real q.val q.property.2))
  let W : Set RealPeriodOneHillPotential := {p | hillOriginalHminusSource p.val∈U}
  have hW : IsOpen W := hU.preimage (hillOriginalHminusSource.continuous.comp continuous_subtype_val)
  refine ⟨P,c,W,hc,hMc,hshift,hW,hqU,H,?_⟩
  intro p hp n w A B γ hγ hpos hneg
  have h := hpull _ hp n w A B γ hγ hpos hneg
  have he : (fun E => P.prescribedDifferential n w (E,hillOriginalHminusSource p.val))=
      (fun E => hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos E/
        prescribedSquareRoot (hillL2Radicand (SpectralWeight.one.toCoeff p.val)) w E) := by
    funext E
    exact P.prescribedDifferential_eq_original p (hUP hp) hreal (houtside _ (hUP hp).1) c hshift n w E
  rw [he] at h
  exact h

end NLS.KdV
