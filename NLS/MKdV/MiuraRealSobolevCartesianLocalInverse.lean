import NLS.MKdV.MiuraRealSobolevCartesianMap

/-! # Physical real nonlinear inverse charts in every native integer Sobolev norm -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Both exact inverse identities hold on full open real native Banach
neighborhoods of zero at every integer Sobolev order. -/
theorem exists_miuraPhysicalSobolevCartesian_localInverse_at_zero (s : ℕ) :
    ∃ U : Set (MiuraRealSobolevSource s), ∃ V : Set (MiuraRealSobolevCartesianTarget s),
      IsOpen U ∧ IsOpen V ∧ (0 : MiuraRealSobolevSource s) ∈ U ∧ (0 : MiuraRealSobolevCartesianTarget s) ∈ V ∧
      miuraPhysicalSobolevCartesianMap s '' U = V ∧ BijOn (miuraPhysicalSobolevCartesianMap s) U V ∧
      ∃ G : MiuraRealSobolevCartesianTarget s → MiuraRealSobolevSource s,
        AnalyticOnNhd ℝ (miuraPhysicalSobolevCartesianMap s) U ∧ AnalyticOnNhd ℝ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraPhysicalSobolevCartesianMap s a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraPhysicalSobolevCartesianMap s (G z) = z) := by
  exact @exists_real_analytic_inverse_neighborhoods_of_fderiv_equiv
    (MiuraRealSobolevSource s) (MiuraRealSobolevCartesianTarget s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (miuraPhysicalSobolevCartesianMap s) (analyticAt_miuraPhysicalSobolevCartesianMap s 0)
    (miuraSobolevCartesianRealFreeEquiv s) (fderiv_miuraPhysicalSobolevCartesianMap_zero s) (miuraPhysicalSobolevCartesianMap_zero s)

/-- All native complex inverse germs preserve physical reality on nearby
real native target data, including closed actions and zero mean. -/
theorem miuraSobolevPositiveCartesian_complex_inverse_real_germ (s : ℕ)
    (g : MiuraPositiveSobolevTarget s → ScalarSobolev s)
    (hl : ∀ᶠ b in 𝓝 (0 : ScalarSobolev s), g (miuraSobolevPositiveCartesianMap s b) = b) :
    ∀ᶠ z in 𝓝 (0 : MiuraRealSobolevCartesianTarget s), g z.val ∈ MiuraRealSobolevSource s := by
  obtain ⟨_,V,_,hV,_,h0V,_,_,G,_,hGA,hG0,_,hG⟩ := exists_miuraPhysicalSobolevCartesian_localInverse_at_zero s
  have hbase : G (miuraPhysicalSobolevCartesianMap s 0) = 0 := by rw [miuraPhysicalSobolevCartesianMap_zero,hG0]
  have hc : ContinuousAt G (miuraPhysicalSobolevCartesianMap s 0) := by
    rw [miuraPhysicalSobolevCartesianMap_zero]
    exact (hGA 0 h0V).continuousAt
  have hr : ∀ᶠ z in 𝓝 (miuraPhysicalSobolevCartesianMap s 0), miuraPhysicalSobolevCartesianMap s (G z) = z := by
    rw [miuraPhysicalSobolevCartesianMap_zero]
    filter_upwards [hV.mem_nhds h0V] with z hz
    exact (hG z hz).2
  have he := inverse_germ_preserves_subspace
    (fun b : MiuraRealSobolevSource s => b.val) continuous_subtype_val
    (fun z : MiuraRealSobolevCartesianTarget s => z.val) (miuraSobolevPositiveCartesianMap s) (miuraPhysicalSobolevCartesianMap s)
    0 g G hc hbase hl hr (miuraPhysicalSobolevCartesianMap_inclusion s)
    (fun b => b ∈ MiuraRealSobolevSource s) (fun b => b.property)
  simpa only [miuraPhysicalSobolevCartesianMap_zero] using he

end NLS.MKdV
