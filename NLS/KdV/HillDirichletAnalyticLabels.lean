import NLS.KdV.HillDirichletNormingData

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem eventually_hillDirichletEnergy_eq_branch_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)))
    (n : ℕ) (hn : 1≤n) (t0 : T) (a : T → ℂ) (ha : ContinuousAt a t0)
    (ha0 : a t0=(hillDirichletEnergy (Q t0) (hq t0) (hr t0) n hn : ℂ))
    (hz : ∀ᶠ t in 𝓝 t0, hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) (a t)=0) :
    ∀ᶠ t in 𝓝 t0, (hillDirichletEnergy (Q t) (hq t) (hr t) n hn : ℂ)=a t := by
  let L (j : ℕ) (t : T) := hillRealLabels (Q t) (hq t) (hr t) j
  have hL (j : ℕ) : Continuous (L j) := continuous_hillRealLabels_family Q hQ hq hr j
  have hm := hillDirichletEnergy_mem_gap (Q t0) (hq t0) (hr t0) n hn
  have hac : ContinuousAt (fun t => (a t).re) t0 := Complex.continuous_re.continuousAt.comp ha
  have hl : L (2*n-2) t0 < (a t0).re := by
    rw [ha0,Complex.ofReal_re]
    have hb := hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) (n-1)
    rw [show 2*(n-1)=2*n-2 by omega,show 2*n-2+1=2*n-1 by omega] at hb
    exact lt_of_lt_of_le hb hm.1
  have hu : (a t0).re < L (2*n+1) t0 := by
    rw [ha0,Complex.ofReal_re]
    exact lt_of_le_of_lt hm.2 (hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) n)
  have hc : ∀ᶠ t in 𝓝 t0, (a t).re∈Ioo (L (2*n-2) t) (L (2*n+1) t) :=
    ((hL _).continuousAt.eventually_lt hac hl).and (hac.eventually_lt (hL _).continuousAt hu)
  filter_upwards [hz,hc] with t ht hct
  have hreal := hillL2DirichletCharacteristic_zero_real _ (hr t) (a t) ht
  have he : ((a t).re : ℂ)=a t := by apply Complex.ext <;> simp [hreal]
  have hz' : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) ((a t).re)=0 := by rw [he];exact ht
  have hmem := hillDirichlet_zero_mem_gap_of_between_neighbor_bands (Q t) (hq t) (hr t) n hn _ hct hz'
  rw [hillDirichletEnergy_eq_of_zero_in_gap (Q t) (hq t) (hr t) n hn _ hmem hz',he]

theorem exists_hillDirichletEnergy_analytic_extension
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a : Coeff 2 → ℂ, AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) ∧
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (SpectralWeight.one.toCoeff p.val)=(hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) := by
  obtain ⟨a,ha,hax,hroot⟩ := exists_hillL2Dirichlet_analytic_root_branch
    (SpectralWeight.one.toCoeff q.val) q.property.2 _ (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  refine ⟨a,ha,hax,hroot,?_⟩
  have hP : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hmatch := eventually_hillDirichletEnergy_eq_branch_family Subtype.val continuous_subtype_val
    (fun p => p.property.1) (fun p => p.property.2) n hn q
    (fun p => a (SpectralWeight.one.toCoeff p.val)) (ha.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) hP.continuousAt) hax
    (hP.continuousAt.tendsto.eventually hroot)
  exact hmatch.mono (fun _ hp => hp.symm)

end NLS.KdV
