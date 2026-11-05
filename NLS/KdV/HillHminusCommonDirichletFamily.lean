import NLS.KdV.HillHminusDirichletCoordinateCharts
import NLS.SequenceSpaces.UniformPositiveFrequencyNonzero

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- One common complex source neighborhood supports ALL actual scalar
Dirichlet energies, all actual root identities, and a uniform full L2
bound on their signed frequency displacement. -/
theorem exists_common_dirichlet_family (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    ∃ R : ℝ, 0<R ∧ ∃ V : Set PeriodOneHminusOne,
      IsOpen V ∧ q∈V ∧ V⊆P.source ∧
      AnalyticOnNhd ℂ P.dirichletDisplacement V ∧
      (∀ a∈V, ‖P.dirichletDisplacement a‖≤R) ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (P.dirichletEnergy n) V ∧
        ∀ a∈V, P.dirichletFrequency (n:ℕ) a≠0 ∧
          hillHminusDirichlet a (P.dirichletEnergy n a)=0 := by
  obtain ⟨U,hU,hqU,hUP,hdisp,hfreq⟩ := P.exists_common_dirichletDisplacement_analytic q hq hreal
  have he (a : PeriodOneHminusOne) (n : ℕ+) :
      (Real.pi:ℂ)*(n:ℕ)+P.dirichletDisplacement a ((n:ℕ):ℤ)=P.dirichletFrequency (n:ℕ) a := by
    change (Real.pi:ℂ)*(n:ℕ)+hillMiuraDirichletDisplacement (P.miura.lift a) ((n:ℕ):ℤ)=_
    rw [hillMiuraDirichletDisplacement_apply]
    simp only [Int.cast_natCast]
    change (Real.pi:ℂ)*(n:ℕ)+(P.dirichletFrequency (n:ℕ) a-(Real.pi:ℂ)*(n:ℕ))=_
    ring
  let u : PeriodOneRealL2 := ⟨P.miura.lift q,hreal⟩
  have hbase (n : ℕ+) : (Real.pi:ℂ)*(n:ℕ)+P.dirichletDisplacement q ((n:ℕ):ℤ)≠0 := by
    rw [he]
    have hp := hillMiura_positive_gap_left_pos u (n:ℕ) (by exact_mod_cast n.pos)
    have hg := hillMiuraDiracDirichlet_mem_gap u (n:ℕ)
    have hx : 0<(P.dirichletFrequency (n:ℕ) q).re := hp.trans_le hg.1
    intro hz
    rw [hz,zero_re] at hx
    exact lt_irrefl 0 hx
  obtain ⟨R,hR,W,hW,hqW,hbound,hne⟩ := exists_local_uniform_positive_frequencies_ne_zero
    P.dirichletDisplacement q (hdisp q hqU).continuousAt hbase
  let V := U∩W
  have hVP : V⊆P.source := fun a ha => hUP ha.1
  refine ⟨R,hR,V,hU.inter hW,⟨hqU,hqW⟩,hVP,hdisp.mono inter_subset_left,
    (fun a ha => hbound a ha.2),?_⟩
  intro n
  have henergy : AnalyticOnNhd ℂ (P.dirichletEnergy n) V := by
    intro a ha
    rw [show P.dirichletEnergy n=(fun b => (P.dirichletFrequency (n:ℕ) b)^2-P.miura.energyShift) from rfl]
    exact ((hfreq (n:ℕ) a ha.1).pow 2).sub analyticAt_const
  refine ⟨henergy,?_⟩
  intro a ha
  have hnz := hne n a ha.2
  rw [he] at hnz
  exact ⟨hnz,hillHminusDirichlet_miuraDirichletEnergy_eq_zero a (P.miura.lift a)
    P.miura.energyShift (P.miura.image _ (hVP ha).1) (n:ℕ) hnz⟩

/-- The actual signed frequency displacement has locally uniform o(1)
tails on complex source neighborhoods, before every distant signed index. -/
theorem exists_local_uniform_small_dirichletFrequency_displacement (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k))
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℕ, ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q∈V ∧ V⊆P.source ∧
      ∀ a∈V, ∀ n : ℤ, K<n.natAbs → ‖P.dirichletFrequency n a-(Real.pi:ℂ)*n‖<ε := by
  obtain ⟨U,hU,hqU,hUP,hdisp,_⟩ := P.exists_common_dirichletDisplacement_analytic q hq hreal
  obtain ⟨K,W,hW,hqW,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates
    (by norm_num : (2:ℝ≥0∞)≠⊤) P.dirichletDisplacement q (hdisp q hqU).continuousAt ε hε
  refine ⟨K,U∩W,hU.inter hW,⟨hqU,hqW⟩,(fun a ha => hUP ha.1),?_⟩
  intro a ha n hn
  have h := hsmall a ha.2 n hn
  change ‖hillMiuraDirichletDisplacement (P.miura.lift a) n‖<ε at h
  rw [hillMiuraDirichletDisplacement_apply] at h
  exact h

end HillHminusPsiChart
end NLS.KdV
