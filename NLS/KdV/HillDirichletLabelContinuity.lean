import NLS.KdV.HillDirichletLabels

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem continuous_hillDirichletEnergy_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)))
    (n : ℕ) (hn : 1≤n) :
    Continuous (fun t => hillDirichletEnergy (Q t) (hq t) (hr t) n hn) := by
  apply continuous_iff_continuousAt.mpr
  intro t0
  let L (j : ℕ) (t : T) := hillRealLabels (Q t) (hq t) (hr t) j
  let P (t : T) := SpectralWeight.one.toCoeff (Q t)
  let x := hillDirichletEnergy (Q t0) (hq t0) (hr t0) n hn
  have hx := hillDirichletEnergy_mem_gap (Q t0) (hq t0) (hr t0) n hn
  have hzero := hillDirichletEnergy_zero (Q t0) (hq t0) (hr t0) n hn
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp hQ
  have hL (j : ℕ) : Continuous (L j) := continuous_hillRealLabels_family Q hQ hq hr j
  obtain ⟨a,ha,hax,he⟩ := exists_hillL2Dirichlet_analytic_real_root_branch (P t0) (hr t0) x hzero
  have hbranch : ∀ᶠ t in 𝓝 t0,
      hillL2DirichletCharacteristic (P t) (a (P t))=0 ∧ (a (P t)).im=0 := by
    filter_upwards [hP.continuousAt.tendsto.eventually he] with t ht
    exact ⟨ht.1,ht.2 (hr t)⟩
  have hac : ContinuousAt (fun t => (a (P t)).re) t0 :=
    Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp hP.continuousAt)
  have hleft : L (2*n-2) t0 < (a (P t0)).re := by
    have hb := hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) (n-1)
    rw [show 2*(n-1)=2*n-2 by omega,show 2*n-2+1=2*n-1 by omega] at hb
    rw [hax,Complex.ofReal_re]
    exact lt_of_lt_of_le hb hx.1
  have hright : (a (P t0)).re < L (2*n+1) t0 := by
    rw [hax,Complex.ofReal_re]
    exact lt_of_le_of_lt hx.2 (hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) n)
  have hcollar : ∀ᶠ t in 𝓝 t0, (a (P t)).re ∈ Ioo (L (2*n-2) t) (L (2*n+1) t) :=
    ((hL _).continuousAt.eventually_lt hac hleft).and
      (hac.eventually_lt (hL _).continuousAt hright)
  have heq : (fun t => hillDirichletEnergy (Q t) (hq t) (hr t) n hn) =ᶠ[𝓝 t0]
      (fun t => (a (P t)).re) := by
    filter_upwards [hbranch,hcollar] with t ht hc
    have heq : ((a (P t)).re : ℂ)=a (P t) := by apply Complex.ext <;> simp [ht.2]
    have hz : hillL2DirichletCharacteristic (P t) ((a (P t)).re)=0 := by rw [heq];exact ht.1
    exact hillDirichletEnergy_eq_of_zero_in_gap (Q t) (hq t) (hr t) n hn _
      (hillDirichlet_zero_mem_gap_of_between_neighbor_bands (Q t) (hq t) (hr t) n hn _ hc hz) hz
  have hvalue : hillDirichletEnergy (Q t0) (hq t0) (hr t0) n hn=(a (P t0)).re := by
    rw [hax,Complex.ofReal_re]
  change Tendsto (fun t => hillDirichletEnergy (Q t) (hq t) (hr t) n hn)
    (𝓝 t0) (𝓝 (hillDirichletEnergy (Q t0) (hq t0) (hr t0) n hn))
  rw [hvalue]
  exact hac.tendsto.congr' heq.symm

theorem continuous_hillDirichletEnergy (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletEnergy q.val q.property.1 q.property.2 n hn) :=
  continuous_hillDirichletEnergy_family Subtype.val continuous_subtype_val
    (fun q => q.property.1) (fun q => q.property.2) n hn

theorem hillDirichletEnergy_lt_succ
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillDirichletEnergy q hq hr n hn < hillDirichletEnergy q hq hr (n+1) (by omega) := by
  have hx := hillDirichletEnergy_mem_gap q hq hr n hn
  have hy := hillDirichletEnergy_mem_gap q hq hr (n+1) (by omega)
  have hi : 2*(n+1)-1=2*n+1 := by omega
  rw [hi] at hy
  exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le (hillRealLabels_band_strict q hq hr n) hy.1)

theorem hillDirichletEnergy_zero_potential
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1≤n) : hillDirichletEnergy 0 hq hr n hn=freeHillValue n := by
  have hx := hillDirichletEnergy_mem_gap 0 hq hr n hn
  rw [hillRealLabels_zero,hillRealLabels_zero] at hx
  have hl : (2*n-1+1)/2=n := by omega
  have hu : (2*n+1)/2=n := by omega
  rw [hl,hu] at hx
  exact le_antisymm hx.2 hx.1

end NLS.KdV
