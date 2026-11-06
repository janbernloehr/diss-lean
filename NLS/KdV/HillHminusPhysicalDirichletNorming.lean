import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.KdV.HillHminusOneDirichletLogNorming
import NLS.MKdV.MiuraL2DirichletTerminal
import NLS.MKdV.L2QuasiHillEnergyAgreement

/-! # Exact physical normalization of the rough Dirichlet normings

At a Dirichlet zero the Miura gauge term vanishes, so the actual terminal
quasi-derivative equals the physical derivative. This identifies the intrinsic
H^-1 endpoint factor and its signed real logarithm with the original physical
L2 definitions, at every source and positive index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open MeasureTheory hiding extend
open NLS.LinearVolterra NLS.MKdV NLS.Fourier
namespace NLS.KdV

theorem HillHminusMiuraChart.physicalMomentum_terminal_eq_quasi
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (E : ℂ) :
    extend (C.physicalMomentum q E (0,1)) 1 =
      quasiHillL2DirichletTerminal (C.lift q) (E+C.energyShift) := by
  calc
    _ = C.physicalMomentum q E (0,1) ⟨1,by constructor <;> norm_num⟩ := extend_coe _ _
    _ = _ := by
      change (l2QuasiHillSolution (unitL2SynthesisEquiv (C.lift q))
        (E+C.energyShift) (0,1) ⟨1,by constructor <;> norm_num⟩).2 = _
      rw [← quasiHillL2SolutionCurve_eq_physical]
      rfl

/-- Comparison holds at every complex L2 source and every actual Dirichlet root. -/
theorem HillHminusMiuraChart.physicalMomentum_terminal_eq_physical_of_root
    (C : HillHminusMiuraChart) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ C.domain) (E : ℂ)
    (hz : hillHminusDirichlet (periodOneL2Inclusion q) E = 0) :
    extend (C.physicalMomentum (periodOneL2Inclusion q) E (0,1)) 1 =
      hillL2DirichletSlope (Coeff.periodDouble q) E := by
  rw [C.physicalMomentum_terminal_eq_quasi,← hillL2DirichletTerminal_eq_slope]
  apply quasiHillL2DirichletTerminal_eq_hillL2_of_shifted_root
  · rw [map_add]
    exact C.image _ hq
  · change C.dirichlet (E,periodOneL2Inclusion q) = 0
    rw [← hillHminusDirichlet_eq_chart C _ hq]
    exact hz

theorem hillHminusDirichletNorming_eq_physical (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillHminusDirichletNorming (hillPhysicalHminusEmbedding p).val
        (hillPhysicalHminusEmbedding p).property n =
      hillL2DirichletSlope (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property) := by
  let q := Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val)
  let C := hillHminusMiuraChartAt (hillPhysicalHminusEmbedding p).val
  have he := C.physicalMomentum_terminal_eq_physical_of_root q
    (mem_hillHminusMiuraChartAt _) _
    (hillHminusDirichletEnergy_zero (hillPhysicalHminusEmbedding p).val
      (hillPhysicalHminusEmbedding p).property n)
  change hillHminusDirichletNorming (hillPhysicalHminusEmbedding p).val
    (hillPhysicalHminusEmbedding p).property n = _ at he
  rw [hillHminusDirichletEnergy_eq_physical,
    show Coeff.periodDouble q = SpectralWeight.one.toCoeff p.val from
      hillPeriodDouble_unitSample _ p.property.1] at he
  exact he

theorem hillHminusDirichletLogNorming_eq_physical (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillHminusDirichletLogNorming (hillPhysicalHminusEmbedding p).val
        (hillPhysicalHminusEmbedding p).property n =
      hillDirichletLogMultiplier p.val p.property.1 p.property.2 (n : ℕ) n.property := by
  rw [hillHminusDirichletLogNorming,hillHminusDirichletNorming_eq_physical]
  rfl

end NLS.KdV
