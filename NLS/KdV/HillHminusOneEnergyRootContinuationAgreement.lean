import NLS.KdV.HillHminusOneEnergyRootFreeAgreement

/-! # Agreement with the original continued Hill root near zero

The free normalization persists along actual real radial source paths in
one common complex chart. All nonreal energies are covered simultaneously;
continuity and connectedness give equality on the full common energy
domain. Nonvanishing square-root uniqueness also identifies the full
complex energy/source germs at every such real input.
-/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart

variable (C : HillHminusMiuraChart)
variable {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (H : SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s)
variable {V : Set PeriodOneHminusOne} (hV : IsOpen V) (hVC : V ⊆ C.domain)
variable (hVW : ∀ q ∈ V, C.criticalSource q ∈ W)
variable (h0 : (0 : PeriodOneHminusOne) ∈ V) (hc : C.energyShift.im = 0)
variable (hr : ∀ q ∈ V, periodOneHminusConjugation q = q →
  IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
variable (q : PeriodOneHminusOne) (hq : periodOneHminusConjugation q = q)
variable (hpath : ∀ r ∈ Icc (0 : ℝ) 1, (r : ℂ) • q ∈ V)

include H hV hVC hVW h0 hc hr hq hpath in
theorem energyRoot_eq_continuedRoot_nonreal (energy : ℂ) (hi : energy.im ≠ 0) :
    C.energyRoot q energy = hillHminusContinuedRoot (energy,q) := by
  obtain ⟨_,hCa⟩ := C.energyRoot_joint H hV hVC hVW
  let p : ℝ → ℂ × PeriodOneHminusOne := fun r => (energy,(r : ℂ) • q)
  have hpc : Continuous p := by dsimp only [p]; fun_prop
  have hC (r : ℝ) (hrange : r ∈ Icc (0 : ℝ) 1) : p r ∈ C.energyRootJointDomain V := by
    refine ⟨hpath r hrange,?_⟩
    exact C.nonreal_mem_energyRootDomain _ hc
      (hr _ (hpath r hrange) (periodOneHminusConjugation_real_smul_fixed r q hq)) energy hi
  have hH (r : ℝ) (_ : r ∈ Icc (0 : ℝ) 1) : p r ∈ hillHminusContinuationDomain :=
    nonreal_mem_hillHminusContinuationDomain _
      (periodOneHminusConjugation_real_smul_fixed r q hq) energy hi
  have he := isPreconnected_Icc.eq_of_sq_eq
    (hCa.continuousOn.comp hpc.continuousOn hC)
    (analyticOnNhd_hillHminusContinuedRoot.continuousOn.comp hpc.continuousOn hH)
    (fun r hrange => by
      change C.energyRoot ((r:ℂ) • q) energy ^ 2 = hillHminusContinuedRoot (p r)^2
      rw [C.energyRoot_sq _ (hVC (hpath r hrange)) energy (hC r hrange).2,
        hillHminusContinuedRoot_sq _ (hH r hrange)]
      rfl)
    (fun {r} hrange => hillHminusSourceFamily.root_ne_zero _ (hH r hrange))
    (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by
      change C.energyRoot ((0:ℂ) • q) energy = hillHminusContinuedRoot (energy,(0:ℂ) • q)
      simp only [zero_smul]
      exact C.energyRoot_eq_continuedRoot_at_zero (hVC h0) hc
        (hr 0 h0 periodOneHminusConjugation_zero)
        ⟨C.nonreal_mem_energyRootDomain 0 hc (hr 0 h0 periodOneHminusConjugation_zero) energy hi,
          nonreal_mem_hillHminusContinuationDomain 0 periodOneHminusConjugation_zero energy hi⟩)
  simpa only [Function.comp_apply,p,ofReal_one,one_smul] using
    he (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)

include H hV hVC hVW h0 hc hr hq hpath in
theorem energyRoot_eq_continuedRoot_of_real_segment :
    EqOn (C.energyRoot q) (fun energy => hillHminusContinuedRoot (energy,q))
      (C.energyRootDomain q ∩ {energy | (energy,q) ∈ hillHminusContinuationDomain}) := by
  have hqV : q ∈ V := by simpa only [ofReal_one,one_smul] using hpath 1 (by constructor <;> norm_num)
  have hreal := hr q hqV hq
  have hn := C.energyRoot_eq_continuedRoot_nonreal H hV hVC hVW h0 hc hr q hq hpath
  intro energy he
  by_cases hi : energy.im ≠ 0
  · exact hn energy hi
  · have hrealEnergy : energy.im = 0 := not_ne_iff.mp hi
    have hconn := isPreconnected_of_contains_nonreal
      (D := C.energyRootDomain q ∩ {z | (z,q) ∈ hillHminusContinuationDomain})
      (fun z hz => ⟨C.nonreal_mem_energyRootDomain q hc hreal z hz,
        nonreal_mem_hillHminusContinuationDomain q hq z hz⟩) he hrealEnergy
    have hCa := (C.energyRoot_spectral_real q hreal).2
    have hHa : AnalyticOnNhd ℂ (fun z => hillHminusContinuedRoot (z,q))
        {z : ℂ | (z,q) ∈ hillHminusContinuationDomain} := by
      intro z hz
      exact (analyticOnNhd_hillHminusContinuedRoot _ hz).comp
        (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
    have hI : (I : ℂ) ∈ C.energyRootDomain q ∩ {z | (z,q) ∈ hillHminusContinuationDomain} :=
      ⟨C.nonreal_mem_energyRootDomain q hc hreal I (by simp),
        nonreal_mem_hillHminusContinuationDomain q hq I (by simp)⟩
    exact hconn.eq_of_sq_eq
      ((hCa.mono inter_subset_left).continuousOn) ((hHa.mono inter_subset_right).continuousOn)
      (fun z hz => by
        change C.energyRoot q z ^ 2 = hillHminusContinuedRoot (z,q)^2
        rw [C.energyRoot_sq q (hVC hqV) _ hz.1,hillHminusContinuedRoot_sq _ hz.2]
        rfl)
      (fun {z} hz => hillHminusSourceFamily.root_ne_zero _ hz.2) hI (hn I (by simp)) he

include H hV hVC hVW h0 hc hr hq hpath in
theorem energyRoot_germ_eq_continuedRoot_of_real_segment
    (energy : ℂ) (he : energy ∈ C.energyRootDomain q)
    (hH : (energy,q) ∈ hillHminusContinuationDomain) :
    (fun t : ℂ × PeriodOneHminusOne => C.energyRoot t.2 t.1) =ᶠ[𝓝 (energy,q)]
      hillHminusContinuedRoot := by
  have hqV : q ∈ V := by simpa only [ofReal_one,one_smul] using hpath 1 (by constructor <;> norm_num)
  obtain ⟨hCo,hCa⟩ := C.energyRoot_joint H hV hVC hVW
  have hpoint : (energy,q) ∈ C.energyRootJointDomain V ∩ hillHminusContinuationDomain :=
    ⟨⟨hqV,he⟩,hH⟩
  have hsq : ∀ᶠ t : ℂ × PeriodOneHminusOne in 𝓝 (energy,q),
      C.energyRoot t.2 t.1 ^ 2 = hillHminusContinuedRoot t ^ 2 := by
    filter_upwards [(hCo.inter isOpen_hillHminusContinuationDomain).mem_nhds hpoint] with t ht
    rw [C.energyRoot_sq t.2 (hVC ht.1.1) t.1 ht.1.2,hillHminusContinuedRoot_sq t ht.2]
    rfl
  exact eventuallyEq_of_sq_eq_of_continuousAt _ _ (energy,q)
    (hCa _ hpoint.1).continuousAt (analyticOnNhd_hillHminusContinuedRoot _ hH).continuousAt
    (C.energyRoot_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hr q hq hpath ⟨he,hH⟩)
    (hillHminusSourceFamily.root_ne_zero _ hH) hsq

end HillHminusMiuraChart

/-- One norm ball is chosen before all real inputs and all energies.
The germs in the conclusion are full complex energy/Hminus1 germs. -/
theorem exists_hillHminus_energyRoot_continuation_agreement :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, 0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
      C.energyShift.im = 0 ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, periodOneHminusConjugation q = q →
        ∀ energy ∈ C.energyRootDomain q, (energy,q) ∈ hillHminusContinuationDomain →
          C.energyRoot q energy = hillHminusContinuedRoot (energy,q) ∧
          (fun t : ℂ × PeriodOneHminusOne => C.energyRoot t.2 t.1) =ᶠ[𝓝 (energy,q)]
            hillHminusContinuedRoot := by
  obtain ⟨C,V,W₀,W,s,hV,h0,hVC,_,_,hc,hr,H,hVW,_,_,_⟩ :=
    exists_hillHminus_real_normalized_energy_pullbacks 0 periodOneHminusConjugation_zero
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hV 0 h0
  refine ⟨C,δ,hδ,hball.trans hVC,hc,?_⟩
  intro q hq hreal energy he hH
  have hpath (r : ℝ) (hrange : r ∈ Icc (0:ℝ) 1) : (r:ℂ) • q ∈ V := by
    apply hball
    rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrange.1]
    exact (mul_le_of_le_one_left (norm_nonneg q) hrange.2).trans_lt (mem_ball_zero_iff.mp hq)
  have hrV : ∀ p ∈ V, periodOneHminusConjugation p = p →
      IsRealType (CoeffPair.toMax 2 (C.criticalSource p)) := fun p hp hpr => (hr p (hVC hp) hpr).2
  exact ⟨C.energyRoot_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hrV q hreal hpath ⟨he,hH⟩,
    C.energyRoot_germ_eq_continuedRoot_of_real_segment H hV hVC hVW h0 hc hrV q hreal hpath energy he hH⟩

end NLS.KdV
