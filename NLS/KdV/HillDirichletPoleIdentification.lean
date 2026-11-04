import NLS.KdV.HillDirichletCentralCount
import NLS.KdV.HillDirichletCentralGeometry
import NLS.KdV.HillDirichletSimplicity
import NLS.ComplexAnalysis.SimpleZeroCountExhaustion
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- All zeros inside every sufficiently large central energy circle
are exactly the first k original gap-labelled Dirichlet energies. -/
theorem exists_hillDirichletCharacteristic_central_label_exhaustion :
    ∃ K : ℕ, ∀ k : ℕ, K≤k →
      (∀ E∈sphere (0 : ℂ) ((centralCircleRadius k)^2),
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0) ∧
      ∀ E∈closedBall (0 : ℂ) ((centralCircleRadius k)^2),
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 ↔
          ∃ j : ℕ, j<k ∧ E=(hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ) := by
  let p := SpectralWeight.one.toCoeff q
  let μ : ℕ → ℂ := fun j => hillDirichletEnergy q hq hr (j+1) (by omega)
  obtain ⟨Kc,hKc⟩ := exists_hillDirichletCharacteristic_central_zero_counts ‖p‖
  obtain ⟨Kg,hKg⟩ := exists_hillDirichletEnergy_central_containment q hq hr
  refine ⟨max Kc Kg,?_⟩
  intro k hk
  have hkc : Kc≤k := (le_max_left _ _).trans hk
  have hkg : Kg≤k := (le_max_right _ _).trans hk
  obtain ⟨hb,hcount⟩ := hKc k hkc p le_rfl
  let R := (centralCircleRadius k)^2
  let S := (Finset.range k).image μ
  have hR : 0<R := sq_pos_of_pos (centralCircleRadius_pos k)
  have hS : ∀ a∈S, a∈closedBall (0 : ℂ) R ∧ hillL2DirichletCharacteristic p a=0 := by
    intro a ha
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨ball_subset_closedBall (hKg k hkg j (Finset.mem_range.mp hj)),
      hillDirichletEnergy_zero q hq hr (j+1) (by omega)⟩
  have hinj : Function.Injective μ := by
    intro i j hij
    exact (strictMono_hillDirichletEnergy_sequence q hq hr).injective (Complex.ofReal_injective hij)
  have hcard : S.card=k := by
    rw [Finset.card_image_of_injective _ hinj,Finset.card_range]
  obtain ⟨b,hbmem⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := (0 : ℂ)) |>.mpr hR.le
  have hfinite := finite_analytic_zeros (isCompact_closedBall (0 : ℂ) R)
    (isConnected_closedBall hR.le) ((analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _))
    (sphere_subset_closedBall hbmem) (hb b hbmem)
  have hcover := zero_iff_mem_of_simple_zero_count (hillL2DirichletCharacteristic p)
    (closedBall (0 : ℂ) R) hfinite S hS
    (fun a _ ha => analyticOrderNatAt_hillL2Dirichlet_zero p hr a ha) (hcount.trans hcard.symm)
  refine ⟨hb,?_⟩
  intro E hE
  rw [hcover E hE]
  constructor
  · intro he
    obtain ⟨j,hj,hμ⟩ := Finset.mem_image.mp he
    exact ⟨j,Finset.mem_range.mp hj,hμ.symm⟩
  · rintro ⟨j,hj,rfl⟩
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩

/-- The original rough real Hill Dirichlet spectrum is exhausted by
its gap-labelled energies, with no additional real or nonreal zeros. -/
theorem hillL2DirichletCharacteristic_zero_iff_label (E : ℂ) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 ↔
      ∃ j : ℕ, E=(hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ) := by
  constructor
  · intro hzero
    obtain ⟨K,hK⟩ := exists_hillDirichletCharacteristic_central_label_exhaustion q hq hr
    obtain ⟨k,hk,hbig⟩ := ((eventually_ge_atTop K).and
      (tendsto_hillEnergyCircleRadius.eventually_ge_atTop ‖E‖)).exists
    have hE : E∈closedBall (0 : ℂ) ((centralCircleRadius k)^2) := by
      simpa only [mem_closedBall,dist_zero_right] using hbig
    obtain ⟨j,_,hj⟩ := ((hK k hk).2 E hE).mp hzero
    exact ⟨j,hj⟩
  · rintro ⟨j,rfl⟩
    exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)

end NLS.KdV
