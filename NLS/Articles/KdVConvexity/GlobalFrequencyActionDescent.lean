import NLS.Articles.KdVConvexity.PhysicalFrequencyPairInvariance
import NLS.Articles.KdVConvexity.ArnoldConeMomentGerms
import NLS.SequenceSpaces.RealScalarActionFamilyDescent
import NLS.SequenceSpaces.ScalarActionFamilyGluing

/-! # Common global action descent of the actual frequency corrections

Independent physical pair charts agree on all real action fibers.
Their analytic action factors therefore glue near the entire cone,
including all boundary points, without a uniform frequency bound.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
open NLS.KdV NLS.ZakharovShabat NLS.Articles.KdVKdV2Frequencies
namespace NLS.Articles.KdVConvexity

structure PhysicalFrequencyRealPair (D : GlobalRoughAbelianForwardData) where
  chart : PhysicalFrequencyPairChart D
  point : Coeff 2 × Coeff 2
  mem_domain : point ∈ chart.domain
  real_point : point ∈ Coeff.realPairLocus 2

namespace PhysicalFrequencyRealPair

def actions {D : GlobalRoughAbelianForwardData} (a : PhysicalFrequencyRealPair D) : Coeff 1 :=
  quadraticActionsExponent a.point

theorem exists_common_action_ball {D : GlobalRoughAbelianForwardData} (a : PhysicalFrequencyRealPair D) :
    ∃ r : ℝ, ∃ g : ℕ+ → Coeff 1 → ℂ, 0<r ∧
      (∀ n, AnalyticOnNhd ℂ (g n) (ball a.actions r)) ∧
      (∀ n, g n a.actions=a.chart.correction n a.point) ∧
      ∀ b ∈ ball a.actions r, b ∈ Coeff.nonnegativeLocus 1 →
        ∃ z : Coeff 2 × Coeff 2, z ∈ a.chart.domain ∧ z ∈ Coeff.realPairLocus 2 ∧
          quadraticActionsExponent (q := 1) z=b ∧ ∀ n, g n b=a.chart.correction n z := by
  obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hrec⟩ :=
    Coeff.exists_real_scalar_action_family_chart (p := 2) (q := 1) (by norm_num)
      a.chart.correction a.chart.domain a.chart.domain_open a.chart.analytic_correction
      (fun n z hz w hw hzr hwr ha => (a.chart.correction_eq_of_real_actions a.chart z hz w hw hzr hwr ha n).symm)
      a.point a.mem_domain a.real_point
  have haT : a.actions ∈ T := by
    rw [←himage]
    exact ⟨a.point,hzZ,rfl⟩
  obtain ⟨r0,hr0,hballT⟩ := Metric.isOpen_iff.mp hT a.actions haT
  obtain ⟨r1,hr1,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (p := 2) (q := 1)
    (by norm_num) a.point a.real_point Z hZ hzZ
  let r := min r0 r1
  have hr : 0<r := lt_min hr0 hr1
  refine ⟨r,g,hr,fun n => (hg n).mono ((ball_subset_ball (min_le_left _ _)).trans hballT),
    fun n => hrec n a.point hzZ,?_⟩
  intro b hb hbr
  obtain ⟨z,hz,hzb⟩ := hlift ⟨ball_subset_ball (min_le_right r0 r1) hb,hbr⟩
  exact ⟨z,hZU hz.1,hz.2,hzb,fun n => by rw [←hzb,hrec n z hz.1]⟩

end PhysicalFrequencyRealPair

/-- All actual local source constructions descend to ONE common complex
action neighborhood of the whole nonnegative normalized ell1 cone. -/
theorem exists_global_physical_frequency_action_corrections (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1 ⊆ V ∧
      (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
        z ∈ P.domain → z ∈ Coeff.realPairLocus 2 →
          ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z := by
  classical
  let A := PhysicalFrequencyRealPair D
  choose r g hr hg hcenter hlift using (PhysicalFrequencyRealPair.exists_common_action_ball (D := D))
  have hpos (a : A) : a.actions ∈ Coeff.nonnegativeLocus 1 :=
    Coeff.quadraticActions_mem_nonnegativeLocus a.point a.real_point
  have he (a b : A) (n : ℕ+) (c : Coeff 1)
      (hc : c ∈ ball a.actions (r a) ∩ ball b.actions (r b)) (hcr : c ∈ Coeff.nonnegativeLocus 1) :
      g a n c=g b n c := by
    obtain ⟨z,hz,hzr,hzc,hzg⟩ := hlift a c hc.1 hcr
    obtain ⟨w,hw,hwr,hwc,hwg⟩ := hlift b c hc.2 hcr
    rw [hzg n,hwg n]
    exact a.chart.correction_eq_of_real_actions b.chart z hz w hw hzr hwr (hwc.trans hzc.symm) n
  obtain ⟨G,hG,hlocal,_⟩ := Coeff.exists_analytic_scalar_family_gluing (p := 2) (q := 1)
    (by norm_num) (fun a : A => a.actions) r g hpos hg he
  let V : Set (Coeff 1) := ⋃ a : A, ball a.actions (r a)
  refine ⟨V,G,isOpen_iUnion (fun _ => isOpen_ball),?_,hG,?_⟩
  · intro b hb
    obtain ⟨Ω,I,_hΩ,hΩr,hI,hrec,_hpos,_hsurj⟩ := exists_global_analytic_Arnold_map_onto_cone
    have hbp : baseActionNormalization.symm b ∈ WeightedCoeff.nonnegativeLocus baseActionWeight 1 := by
      apply (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 _).mpr
      change baseActionNormalization (baseActionNormalization.symm b) ∈ Coeff.nonnegativeLocus 1
      rwa [baseActionNormalization.apply_symm_apply]
    obtain ⟨q,hqr,hqm,hqI⟩ := exists_source_of_nonnegative_Arnold_actions Ω hΩr I hI hrec
      (baseActionNormalization.symm b) hbp
    obtain ⟨P,z,hz,hzr,hzq⟩ := exists_physicalFrequencyPairChart D q hqr hqm
    let a : A := ⟨P,z,hz,hzr⟩
    have hza : a.actions=b := by
      have he := Arnold_action_of_pair_inverse_identity D Ω hΩr I hI hrec
        (P.potential z) (P.real_potential z hz hzr) z hzr (P.signed_inverse z hz)
      rw [hzq,hqI] at he
      have hh := congrArg baseActionNormalization he
      rw [baseActionNormalization.apply_symm_apply] at hh
      exact (WeightedCoeff.weight_actionsFromNormalizedCoordinates baseActionWeight z).symm.trans hh.symm
    exact mem_iUnion.mpr ⟨a,by rw [hza]; exact mem_ball_self (hr a)⟩
  · intro P z hz hzr n
    let a : A := ⟨P,z,hz,hzr⟩
    exact (hlocal a n (mem_ball_self (hr a))).trans (hcenter a n)

end NLS.Articles.KdVConvexity
