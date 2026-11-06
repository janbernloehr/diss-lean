import NLS.MKdV.MiuraGeneralCartesianComplexInverse
import NLS.MKdV.MiuraNLSActionsCartesianChart

/-! # The whole original NLS action sequence in general Cartesian inverse charts

The target ball is centered at the actual Cartesian image of the profile.
The inverse is holomorphic, preserves physical reality, and carries the
full original signed NLS action sequence in its genuine summable norm.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraGeneralCartesianNLSActionChart (a : MiuraRealL2) where
  source : Set (Coeff 2)
  radius : ℝ
  inverse : MiuraPositiveCartesianTarget → Coeff 2
  source_open : IsOpen source
  radius_pos : 0 < radius
  source_base : a.val ∈ source
  forward_analytic : AnalyticOnNhd ℂ miuraPositiveCartesianMap source
  inverse_analytic : AnalyticOnNhd ℂ inverse (ball (miuraPositiveCartesianMap a.val) radius)
  inverse_base : inverse (miuraPositiveCartesianMap a.val) = a.val
  left_inverse : ∀ b ∈ source, inverse (miuraPositiveCartesianMap b) = b
  right_inverse : ∀ z ∈ ball (miuraPositiveCartesianMap a.val) radius,
    inverse z ∈ source ∧ miuraPositiveCartesianMap (inverse z) = z
  inverse_real : ∀ z ∈ ball (miuraPositiveCartesianMap a.val) radius,
    z ∈ miuraCartesianRealSubmodule → inverse z ∈ Coeff.physicalRealSubmodule 2
  inverse_action_domain : ∀ z ∈ ball (miuraPositiveCartesianMap a.val) radius,
    inverse z ∈ miuraOriginalNLSActionDomain

private theorem exists_miuraGeneralCartesian_inverse_ball (a : MiuraRealL2)
    (P : OpenPartialHomeomorph (Coeff 2) MiuraPositiveCartesianTarget)
    (hP : (P : Coeff 2 → MiuraPositiveCartesianTarget) = miuraPositiveCartesianMap)
    (haP : a.val ∈ P.source) (hG : AnalyticOnNhd ℂ P.symm P.target)
    (hreal : ∀ᶠ z in 𝓝 (miuraPhysicalCartesianMap a), P.symm z.val ∈ Coeff.physicalRealSubmodule 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ ball (miuraPositiveCartesianMap a.val) R,
      z ∈ P.target ∧ P.symm z ∈ miuraOriginalNLSActionDomain ∧
        (z ∈ miuraCartesianRealSubmodule → P.symm z ∈ Coeff.physicalRealSubmodule 2) := by
  have hzP : miuraPositiveCartesianMap a.val ∈ P.target := by rw [← hP]; exact P.map_source haP
  have hbase : P.symm (miuraPositiveCartesianMap a.val) = a.val := by rw [← hP]; exact P.left_inv haP
  have hnear : ∀ᶠ z in 𝓝 (miuraPositiveCartesianMap a.val),
      z ∈ P.target ∧ P.symm z ∈ miuraOriginalNLSActionDomain := by
    have ht : Tendsto P.symm (𝓝 (miuraPositiveCartesianMap a.val)) (𝓝 a.val) := by
      simpa only [hbase] using (hG _ hzP).continuousAt.tendsto
    filter_upwards [P.open_target.mem_nhds hzP,
      ht.eventually (isOpen_miuraOriginalNLSActionDomain.mem_nhds
        (real_mem_miuraOriginalNLSActionDomain _ a.property))] with z hz hgz
    exact ⟨hz,hgz⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨q,hq,hrealball⟩ := Metric.mem_nhds_iff.mp hreal
  refine ⟨min r q,lt_min hr hq,?_⟩
  intro z hz
  have hzr : z ∈ ball (miuraPositiveCartesianMap a.val) r := by
    change dist z (miuraPositiveCartesianMap a.val) < r
    exact lt_of_lt_of_le hz (min_le_left _ _)
  refine ⟨(hball hzr).1,(hball hzr).2,?_⟩
  intro hzreal
  have hsub : (⟨z,hzreal⟩ : MiuraRealCartesianTarget) ∈ ball (miuraPhysicalCartesianMap a) q := by
    change dist z (miuraPhysicalCartesianMap a).val < q
    rw [miuraPhysicalCartesianMap_inclusion]
    exact lt_of_lt_of_le hz (min_le_right _ _)
  exact hrealball hsub

theorem nonempty_miuraGeneralCartesianNLSActionChart (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Nonempty (MiuraGeneralCartesianNLSActionChart (miuraPhysicalH1L2Point a ha)) := by
  let b := miuraPhysicalH1L2Point a ha
  obtain ⟨P,hP,hb,hM,hG⟩ := exists_miuraPositiveCartesian_analytic_chart_H1 a ha
  have hleft : ∀ᶠ u in 𝓝 (scalarInclusion a), P.symm (miuraPositiveCartesianMap u) = u := by
    filter_upwards [P.open_source.mem_nhds hb] with u hu
    rw [← hP]
    exact P.left_inv hu
  have hreal := miuraPositiveCartesian_complex_inverse_real_germ_H1 a ha P.symm hleft
  obtain ⟨R,hR,hball⟩ := exists_miuraGeneralCartesian_inverse_ball b P hP hb hG hreal
  let U := P.source ∩ miuraPositiveCartesianMap ⁻¹' ball (miuraPositiveCartesianMap b.val) R
  have hU : IsOpen U := hM.continuousOn.isOpen_inter_preimage P.open_source isOpen_ball
  have hbU : b.val ∈ U := ⟨hb,mem_ball_self hR⟩
  have hright (z : MiuraPositiveCartesianTarget) (hz : z ∈ ball (miuraPositiveCartesianMap b.val) R) :
      P.symm z ∈ U ∧ miuraPositiveCartesianMap (P.symm z) = z := by
    have hzP := (hball z hz).1
    have he : miuraPositiveCartesianMap (P.symm z) = z := by rw [← hP]; exact P.right_inv hzP
    refine ⟨⟨P.map_target hzP,?_⟩,he⟩
    change miuraPositiveCartesianMap (P.symm z) ∈ ball (miuraPositiveCartesianMap b.val) R
    rwa [he]
  refine ⟨⟨U,R,P.symm,hU,hR,hbU,fun u hu => hM u hu.1,
    fun z hz => hG z (hball z hz).1,?_,
    fun u hu => by rw [← hP]; exact P.left_inv hu.1,hright,
    fun z hz => (hball z hz).2.2,fun z hz => (hball z hz).2.1⟩⟩
  rw [← hP]
  exact P.left_inv hb

namespace MiuraGeneralCartesianNLSActionChart
variable {a : MiuraRealL2}

def observables (C : MiuraGeneralCartesianNLSActionChart a) (z : MiuraPositiveCartesianTarget) : Coeff 1 :=
  miuraOriginalNLSActionSequence (C.inverse z)

theorem observables_analytic (C : MiuraGeneralCartesianNLSActionChart a) :
    AnalyticOnNhd ℂ C.observables (ball (miuraPositiveCartesianMap a.val) C.radius) := fun z hz =>
  (analyticOnNhd_miuraOriginalNLSActionSequence _ (C.inverse_action_domain z hz)).comp (C.inverse_analytic z hz)

theorem observables_recover (C : MiuraGeneralCartesianNLSActionChart a) (b : Coeff 2) (hb : b ∈ C.source) :
    C.observables (miuraPositiveCartesianMap b) = miuraOriginalNLSActionSequence b := by
  change miuraOriginalNLSActionSequence (C.inverse (miuraPositiveCartesianMap b)) = _
  rw [C.left_inverse b hb]

end MiuraGeneralCartesianNLSActionChart
end NLS.MKdV
