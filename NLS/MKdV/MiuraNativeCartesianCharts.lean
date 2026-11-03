import NLS.MKdV.MiuraSobolevNormalizedCartesian

/-! # Physical real-preserving complex native Cartesian charts at every profile -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraNativeCartesianChart (s : ℕ) (a : MiuraRealSobolevSource s) where
  source : Set (ScalarSobolev s)
  radius : ℝ
  inverse : MiuraPositiveCartesianTarget → ScalarSobolev s
  source_open : IsOpen source
  radius_pos : 0 < radius
  source_base : a.val ∈ source
  forward_analytic : AnalyticOnNhd ℂ (miuraSobolevNormalizedCartesianMap s) source
  inverse_analytic : AnalyticOnNhd ℂ inverse (ball (miuraSobolevNormalizedCartesianMap s a.val) radius)
  inverse_base : inverse (miuraSobolevNormalizedCartesianMap s a.val) = a.val
  left_inverse : ∀ b ∈ source, inverse (miuraSobolevNormalizedCartesianMap s b) = b
  right_inverse : ∀ z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) radius,
    inverse z ∈ source ∧ miuraSobolevNormalizedCartesianMap s (inverse z) = z
  inverse_real : ∀ z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) radius,
    z ∈ miuraCartesianRealSubmodule → inverse z ∈ MiuraRealSobolevSource s

private theorem exists_miuraNativeCartesian_inverse_ball (s : ℕ) (a : MiuraRealSobolevSource s)
    (P : OpenPartialHomeomorph (ScalarSobolev s) MiuraPositiveCartesianTarget)
    (hP : (P : ScalarSobolev s → MiuraPositiveCartesianTarget) = miuraSobolevNormalizedCartesianMap s)
    (haP : a.val ∈ P.source)
    (hreal : ∀ᶠ z in 𝓝 (miuraPhysicalSobolevNormalizedCartesianMap s a),
      P.symm z.val ∈ MiuraRealSobolevSource s) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) R,
      z ∈ P.target ∧ (z ∈ miuraCartesianRealSubmodule → P.symm z ∈ MiuraRealSobolevSource s) := by
  have hzP : miuraSobolevNormalizedCartesianMap s a.val ∈ P.target := by rw [← hP]; exact P.map_source haP
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (P.open_target.mem_nhds hzP)
  obtain ⟨q,hq,hrealball⟩ := Metric.mem_nhds_iff.mp hreal
  refine ⟨min r q,lt_min hr hq,?_⟩
  intro z hz
  have hzr : z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) r := by
    change dist z (miuraSobolevNormalizedCartesianMap s a.val) < r
    exact lt_of_lt_of_le hz (min_le_left _ _)
  refine ⟨hball hzr,?_⟩
  intro hzreal
  have hsub : (⟨z,hzreal⟩ : MiuraRealCartesianTarget) ∈ ball (miuraPhysicalSobolevNormalizedCartesianMap s a) q := by
    change dist z (miuraPhysicalSobolevNormalizedCartesianMap s a).val < q
    rw [miuraPhysicalSobolevNormalizedCartesianMap_inclusion]
    exact lt_of_lt_of_le hz (min_le_right _ _)
  exact hrealball hsub

theorem nonempty_miuraNativeCartesianChart (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    Nonempty (MiuraNativeCartesianChart s a) := by
  obtain ⟨P,hP,ha,hM,hG⟩ := exists_miuraSobolevNormalizedCartesian_analytic_chart s hs a
  have hleft : ∀ᶠ u in 𝓝 a.val, P.symm (miuraSobolevNormalizedCartesianMap s u) = u := by
    filter_upwards [P.open_source.mem_nhds ha] with u hu
    rw [← hP]
    exact P.left_inv hu
  have hreal := miuraSobolevNormalizedCartesian_inverse_real_germ s hs a P.symm hleft
  obtain ⟨R,hR,hball⟩ := exists_miuraNativeCartesian_inverse_ball s a P hP ha hreal
  let U := P.source ∩ miuraSobolevNormalizedCartesianMap s ⁻¹' ball (miuraSobolevNormalizedCartesianMap s a.val) R
  have hU : IsOpen U := hM.continuousOn.isOpen_inter_preimage P.open_source isOpen_ball
  have haU : a.val ∈ U := ⟨ha,mem_ball_self hR⟩
  have hright (z : MiuraPositiveCartesianTarget) (hz : z ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) R) :
      P.symm z ∈ U ∧ miuraSobolevNormalizedCartesianMap s (P.symm z) = z := by
    have hzP := (hball z hz).1
    have he : miuraSobolevNormalizedCartesianMap s (P.symm z) = z := by rw [← hP]; exact P.right_inv hzP
    refine ⟨⟨P.map_target hzP,?_⟩,he⟩
    change miuraSobolevNormalizedCartesianMap s (P.symm z) ∈ ball (miuraSobolevNormalizedCartesianMap s a.val) R
    rwa [he]
  refine ⟨⟨U,R,P.symm,hU,hR,haU,fun u hu => hM u hu.1,
    fun z hz => hG z (hball z hz).1,?_,
    fun u hu => by rw [← hP]; exact P.left_inv hu.1,hright,
    fun z hz => (hball z hz).2⟩⟩
  rw [← hP]
  exact P.left_inv ha

end NLS.MKdV
