import NLS.KdV.HillDirichletSheetRoot
import NLS.KdV.HillRealBands

/-! # Nonzero actual sheet from exclusion of the two Dirichlet endpoints -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem hillDirichletSheetRoot_ne_zero_of_endpoint_characteristics
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1 ≤ k)
    (hleft : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
      (hillRealLabels q.val q.property.1 q.property.2 (2*k-1)) ≠ 0)
    (hright : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val)
      (hillRealLabels q.val q.property.1 q.property.2 (2*k)) ≠ 0) :
    hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k hk) ≠ 0 := by
  let μ := hillDirichletEnergy q.val q.property.1 q.property.2 k hk
  have hmem := hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 k hk
  have hz := hillDirichletEnergy_zero q.val q.property.1 q.property.2 k hk
  have hl : hillRealLabels q.val q.property.1 q.property.2 (2*k-1) < μ := by
    apply lt_of_le_of_ne hmem.1
    intro he
    exact hleft (by rw [← he] at hz;exact hz)
  have hr : μ < hillRealLabels q.val q.property.1 q.property.2 (2*k) := by
    apply lt_of_le_of_ne hmem.2
    intro he
    exact hright (by rw [he] at hz;exact hz)
  have hrad := hillL2Radicand_ne_zero_between_labels q.val q.property.1 q.property.2
    (2*k-1) μ (show μ ∈ Ioo _ _ by
      rw [show 2*k-1+1 = 2*k by omega]
      exact ⟨hl,hr⟩)
  intro hR
  apply hrad
  rw [← hillDirichletSheetRoot_sq_of_characteristic_zero _ _ hz,hR,zero_pow (by norm_num)]

end NLS.KdV
