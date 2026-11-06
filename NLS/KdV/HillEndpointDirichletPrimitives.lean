import NLS.KdV.HillEndpointAngleCotangent
import NLS.KdV.HillEndpointBaseAngles
import NLS.KdV.HillEndpointPrimitiveParameters
import NLS.KdV.HillIsospectralCosinePrimitives
import NLS.ComplexAnalysis.MovingSpectralParameter

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual Dirichlet-evaluated Abelian primitive at a periodic endpoint has
its physical cotangent in the genuine log-norming span. Its analytic germ,
physical terminal matching and cotangent are all constructed together. -/
theorem exists_hillDirichletPrimitive_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ B ε : Coeff 2 → ℂ, ∃ e c : ℂ,
      (e=0 ∨ e=(Real.pi : ℂ)) ∧ AnalyticAt ℂ B (SpectralWeight.one.toCoeff q.val) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q.val) ∧ ε (SpectralWeight.one.toCoeff q.val)=e ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        hillRealGapHalfLength p.val p.property.1 p.property.2 k≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
        B (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k
          (ε (SpectralWeight.one.toCoeff p.val))) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ B (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  obtain ⟨e,he,hpoint,hsin⟩ := exists_hillDirichlet_endpoint_base_angle q k hk hlog
  obtain ⟨d,μ,S,ε,hd,hμ,_,hε,hd0,hμ0,_,hε0,_,_,hcomplex,hterminal⟩ :=
    exists_hillDirichlet_analytic_characteristic_angle_at q.val q.property.1 q.property.2 k hk hgap e hpoint hsin
  have hroot := hcomplex.mono (fun _ hp => hp.2.2.1)
  have htrig := hcomplex.mono (fun _ hp => hp.2.2.2.2.1.trans hp.2.2.2.2.2)
  obtain ⟨c,hcn,hεder⟩ := hillCharacteristicAngle_endpoint_norming_cotangent q k hk hgap hlog
    d μ ε hd hμ hε hd0 hμ0 hroot htrig
  obtain ⟨F,Ω,Z,W,hΩ,_,hangle,hZ,hqZ,hW,hqW,hF,_,hmatch,hD,_⟩ :=
    exists_hillAbelianCosinePrimitive_joint_isospectral_open_gap_chart q.val q.property.1 q.property.2 h0q h0r n k hn hk hgap
  have heΩ : e∈Ω := by
    rcases he with he | he
    · rw [he]
      apply hangle
      simpa only [ofReal_neg,ofReal_zero] using ofReal_mem_ordered_segment (-Real.pi) Real.pi 0
        (by linarith [Real.pi_pos]) ⟨by linarith [Real.pi_pos],Real.pi_pos.le⟩
    · rw [he]
      exact hangle (right_mem_segment ℝ _ _)
  have hFbase : AnalyticAt ℂ F (e,SpectralWeight.one.toCoeff q.val) := hF _ ⟨heΩ,hqZ⟩
  let B : Coeff 2 → ℂ := fun p => F (ε p,p)
  have hB : AnalyticAt ℂ B (SpectralWeight.one.toCoeff q.val) :=
    (hF (ε (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val)
      ⟨by change ε (SpectralWeight.one.toCoeff q.val)∈Ω; rw [hε0]; exact heΩ,hqZ⟩).comp (f := fun p : Coeff 2 => (ε p,p)) (hε.prod analyticAt_id)
  have hFe : AnalyticAt ℂ (fun p : Coeff 2 => F (e,p)) (SpectralWeight.one.toCoeff q.val) :=
    hFbase.comp (f := fun p : Coeff 2 => (e,p)) (analyticAt_const.prod analyticAt_id)
  have hFereal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (e,SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k e :=
    Filter.Eventually.mono (hW.mem_nhds hqW) (fun p hp => (hmatch p hp).2 e heΩ)
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hεΩ : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q, ε (P p)∈Ω :=
    (hε.continuousAt.comp (f := P) hP.continuousAt).preimage_mem_nhds
      (hΩ.mem_nhds (by change ε (SpectralWeight.one.toCoeff q.val)∈Ω; rw [hε0]; exact heΩ))
  refine ⟨B,ε,e,hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k e*c,
    he,hB,hε,hε0,?_,?_⟩
  · filter_upwards [hterminal,hW.mem_nhds hqW,hεΩ] with p hp hpW hpΩ
    exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,(hmatch p hpW).2 _ hpΩ⟩
  · intro h heven
    have hpzero := hillAbelianPrimitive_endpoint_parameter_fderiv_eq_zero q n k hn hk e he
      (fun p => F (e,p)) hFe hFereal h heven
    change (fderiv ℂ (fun p : Coeff 2 => F (ε p,p)) (SpectralWeight.one.toCoeff q.val)) _=_
    rw [fderiv_moving_spectral_parameter F ε (SpectralWeight.one.toCoeff q.val)
      (hF (ε (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val)
        ⟨by change ε (SpectralWeight.one.toCoeff q.val)∈Ω; rw [hε0]; exact heΩ,hqZ⟩).differentiableAt hε.differentiableAt]
    simp only [add_apply,smul_apply,smul_eq_mul]
    rw [hε0,hpzero,(hD e heΩ).deriv,hεder,zero_add]
    ring

end NLS.KdV
