import NLS.KdV.HillActionAngleOriginalEnergyBound

/-! ONE common open connected complex neighborhood of the ENTIRE real
native source form supports analytic ACTUAL Cartesian formulas and the
ORIGINAL energy-weight estimate locally uniformly BEFORE ALL n. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

structure HillActionAngleEnergyBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusActionAmplitudeDomain ∩
    (hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalDirichletDomain)
  bound : ℝ
  bound_pos : 0 < bound
  factors : ∀ q ∈ ball center radius, ∀ n : ℕ+,
    ‖hillHminusActionAngleFactorPlus n q‖ ≤ (bound/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q ∧
    ‖hillHminusActionAngleFactorMinus n q‖ ≤ (bound/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n q

namespace HillActionAngleEnergyBall

def source (B : HillActionAngleEnergyBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillActionAngleEnergyBall) : IsOpen B.source := isOpen_ball

end HillActionAngleEnergyBall

theorem exists_hillActionAngleEnergyBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillActionAngleEnergyBall, q ∈ B.source := by
  obtain ⟨U,hU,hqU,hUD,C,hC,hbound⟩ := exists_local_uniform_actionAngle_original_energy_bound q hr
  have hqZ := real_mem_hillHminusCanonicalZeroSequenceDomain q hr
  have hqD := real_mem_hillHminusCanonicalDirichletDomain q hr
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp
    ((hU.inter (isOpen_hillHminusCanonicalZeroSequenceDomain.inter isOpen_hillHminusCanonicalDirichletDomain)).mem_nhds
      ⟨hqU,hqZ,hqD⟩)
  refine ⟨⟨q,hr,r,hrpos,(fun _ h => ⟨hUD (hball h).1,(hball h).2⟩),C,hC,?_⟩,mem_ball_self hrpos⟩
  intro a ha n
  have h := hbound a (hball ha).1 n
  exact ⟨h.1,h.2.1⟩

def hillHminusActionAngleEnergyDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillActionAngleEnergyBall, B.source

theorem isOpen_hillHminusActionAngleEnergyDomain : IsOpen hillHminusActionAngleEnergyDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusActionAngleEnergyDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusActionAngleEnergyDomain := by
  obtain ⟨B,hB⟩ := exists_hillActionAngleEnergyBall q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem hillHminusActionAngleEnergyDomain_subset :
    hillHminusActionAngleEnergyDomain ⊆ hillHminusActionAmplitudeDomain ∩
      (hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalDirichletDomain) := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem analyticOnNhd_hillHminusActionAngle_on_energy_domain (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionAngleX n) hillHminusActionAngleEnergyDomain ∧
      AnalyticOnNhd ℂ (hillHminusActionAngleY n) hillHminusActionAngleEnergyDomain :=
  ⟨(analyticOnNhd_hillHminusActionAngleX n).mono (fun _ h => (hillHminusActionAngleEnergyDomain_subset h).1),
    (analyticOnNhd_hillHminusActionAngleY n).mono (fun _ h => (hillHminusActionAngleEnergyDomain_subset h).1)⟩

theorem exists_locally_uniform_actionAngle_original_energy_bound :
    ∀ q ∈ hillHminusActionAngleEnergyDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleEnergyDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ U, ∀ n : ℕ+,
        ‖hillHminusActionAngleFactorPlus n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleFactorMinus n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleX n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y ∧
        ‖hillHminusActionAngleY n y‖ ≤ (C/Real.sqrt (n:ℕ))*hillHminusCanonicalCartesianWeight n y := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  refine ⟨B.source,B.source_open,hB,(fun _ h => mem_iUnion.mpr ⟨B,h⟩),B.bound,B.bound_pos,?_⟩
  intro y hy n
  have h := B.factors y hy n
  exact ⟨h.1,h.2,norm_hillHminusActionAngleXY_le_of_factor_bounds n y _ h.1 h.2⟩

theorem isConnected_hillHminusActionAngleEnergyDomain : IsConnected hillHminusActionAngleEnergyDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillActionAngleEnergyBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball _ _).isPreconnected
  have hcommon : (⋂ B : HillActionAngleEnergyBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillActionAngleEnergyBall, S ∪ B.source) = hillHminusActionAngleEnergyDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusActionAngleEnergyDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusActionAngleEnergyDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
