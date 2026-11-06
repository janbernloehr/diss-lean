import NLS.KdV.HillDirichletTerminalVariation
import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # The actual filled Dirichlet kernel is jointly analytic -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- Actual entire divided difference, normalized at a moving simple
Dirichlet energy. The integral definition fills the spectral diagonal. -/
def hillComplexDirichletGardnerKernel (a : Coeff 2 → ℂ) (t : ℂ × Coeff 2) : ℂ :=
  -parametricMovingDividedDifference (fun s : ℂ × Coeff 2 => hillL2DirichletCharacteristic s.2 s.1) a t/
    (2*deriv (hillL2DirichletCharacteristic t.2) (a t.2))

theorem analyticOnNhd_hillComplexDirichletGardnerKernel
    (a : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hV : IsOpen V) (ha : AnalyticOnNhd ℂ a V)
    (hne : ∀ p∈V, deriv (hillL2DirichletCharacteristic p) (a p)≠0) :
    AnalyticOnNhd ℂ (hillComplexDirichletGardnerKernel a) (univ ×ˢ V) := by
  let F : ℂ × Coeff 2 → ℂ := fun t => hillL2DirichletCharacteristic t.2 t.1
  have hF : AnalyticOnNhd ℂ F (univ ×ˢ V) := analyticOnNhd_hillL2DirichletCharacteristic_joint.mono (subset_univ _)
  have hDD := analyticOnNhd_parametricMovingDividedDifference F a hV hF ha
  have hJ := analyticOnNhd_spectral_deriv_of_analyticOnNhd F (univ : Set (ℂ × Coeff 2))
    isOpen_univ analyticOnNhd_hillL2DirichletCharacteristic_joint
  intro t ht
  have hgraph : AnalyticAt ℂ (fun s : ℂ × Coeff 2 => (a s.2,s.2)) t :=
    ((ha t.2 ht.2).comp (f := fun s : ℂ × Coeff 2 => s.2) analyticAt_snd).prod analyticAt_snd
  have hden : AnalyticAt ℂ (fun s : ℂ × Coeff 2 => deriv (hillL2DirichletCharacteristic s.2) (a s.2)) t :=
    (hJ (a t.2,t.2) (mem_univ _)).comp (f := fun s : ℂ × Coeff 2 => (a s.2,s.2)) hgraph
  exact (hDD t ht).neg.div (analyticAt_const.mul hden)
    (mul_ne_zero (by norm_num) (hne t.2 ht.2))

/-- At a physical real source this is exactly the actual filled kernel,
including its value -1/2 on the spectral diagonal. -/
theorem hillComplexDirichletGardnerKernel_eq_real
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (b : ℂ) :
    hillComplexDirichletGardnerKernel a (b,SpectralWeight.one.toCoeff q.val)=hillDirichletGardnerKernel q k hk b := by
  let V := {p : Coeff 2 | AnalyticAt ℂ a p}
  let F : ℂ × Coeff 2 → ℂ := fun t => hillL2DirichletCharacteristic t.2 t.1
  have hF : AnalyticOnNhd ℂ F (univ ×ˢ V) := analyticOnNhd_hillL2DirichletCharacteristic_joint.mono (subset_univ _)
  have hμ : AnalyticOnNhd ℂ a V := fun _ hp => hp
  have hDD := parametricMovingDividedDifference_eq_dslope F a hF hμ b (SpectralWeight.one.toCoeff q.val) ha
  have hz := hillDirichletEnergy_zero q.val q.property.1 q.property.2 k hk
  have hd := hillL2DirichletCharacteristic_deriv_ne_zero (SpectralWeight.one.toCoeff q.val) q.property.2 _ hz
  unfold hillComplexDirichletGardnerKernel hillDirichletGardnerKernel
  rw [hDD,ha0]
  dsimp only [F]
  split_ifs with hb
  · rw [hb,dslope_same]
    field_simp
  · rw [dslope_of_ne _ hb,slope_def_field,hz,sub_zero]
    field_simp
    ring

theorem exists_hillDirichletGardnerKernel_joint_analytic_chart
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) :
    ∃ a : Coeff 2 → ℂ, ∃ V : Set (Coeff 2), IsOpen V ∧ SpectralWeight.one.toCoeff q.val∈V ∧
      AnalyticOnNhd ℂ a V ∧
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p)=0) ∧
      AnalyticOnNhd ℂ (hillComplexDirichletGardnerKernel a) (univ ×ˢ V) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        SpectralWeight.one.toCoeff p.val∈V ∧ ∀ b : ℂ,
          hillComplexDirichletGardnerKernel a (b,SpectralWeight.one.toCoeff p.val)=hillDirichletGardnerKernel p k hk b := by
  obtain ⟨a,ha,ha0,haz,hamatch⟩ := exists_hillDirichletEnergy_analytic_extension q k hk
  let J : Coeff 2 → ℂ := fun p => deriv (hillL2DirichletCharacteristic p) (a p)
  have hJ : AnalyticAt ℂ J (SpectralWeight.one.toCoeff q.val) :=
    ((analyticOnNhd_spectral_deriv_of_analyticOnNhd
      (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) univ isOpen_univ
      analyticOnNhd_hillL2DirichletCharacteristic_joint) _ (mem_univ _)).comp
        (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
  have hJn : J (SpectralWeight.one.toCoeff q.val)≠0 := by
    change deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val))
      (a (SpectralWeight.one.toCoeff q.val))≠0
    rw [ha0]
    exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _ (hillDirichletEnergy_zero q.val q.property.1 q.property.2 k hk)
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp (hJ.continuousAt.eventually_ne hJn)
  let V := W ∩ {p : Coeff 2 | AnalyticAt ℂ a p}
  have hV : IsOpen V := hW.inter (isOpen_analyticAt ℂ a)
  have hqV : SpectralWeight.one.toCoeff q.val∈V := ⟨hqW,ha⟩
  have haV : AnalyticOnNhd ℂ a V := fun _ hp => hp.2
  refine ⟨a,V,hV,hqV,haV,haz,analyticOnNhd_hillComplexDirichletGardnerKernel a V hV haV
    (fun p hp => hWsub hp.1),?_⟩
  have hP : Continuous (fun p : RealPeriodOneHillPotential => SpectralWeight.one.toCoeff p.val) :=
    SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  filter_upwards [hamatch,hP.continuousAt.preimage_mem_nhds (hV.mem_nhds hqV)] with p hp hpV
  exact ⟨hpV,fun b => hillComplexDirichletGardnerKernel_eq_real p k hk a (haV _ hpV) hp b⟩

/-- The literal filled physical kernel is entire in its spectral argument. -/
theorem analyticOnNhd_hillDirichletGardnerKernel (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k) :
    AnalyticOnNhd ℂ (hillDirichletGardnerKernel q k hk) univ := by
  obtain ⟨a,V,_,hqV,_,_,hK,hmatch⟩ := exists_hillDirichletGardnerKernel_joint_analytic_chart q k hk
  have he := (Filter.Eventually.self_of_nhds (x := q) hmatch).2
  intro b _
  have ha := (hK (b,SpectralWeight.one.toCoeff q.val) ⟨mem_univ _,hqV⟩).comp
    (f := fun z : ℂ => (z,SpectralWeight.one.toCoeff q.val)) (analyticAt_id.prod analyticAt_const)
  exact ha.congr (Filter.Eventually.of_forall (fun z => he z))

end NLS.KdV
