import NLS.KdV.HillHminusPhysicalDirichletLabels
import NLS.SequenceSpaces.OrderedNatEnumerationUnique

/-! # All rough periodic labels restrict to the original physical labels -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusRadicand_eq_physical (p : RealPeriodOneHillPotential) :
    hillHminusRadicand (hillPhysicalHminusEmbedding p).val =
      hillL2Radicand (SpectralWeight.one.toCoeff p.val) := by
  funext E
  change hillHminusRadicand (periodOneL2Inclusion _) E = _
  rw [hillHminusRadicand_eq_hillL2,hillPeriodDouble_unitSample _ p.property.1]

theorem hillHminusRealLabels_eq_physical (p : RealPeriodOneHillPotential) :
    hillHminusRealLabels (hillPhysicalHminusEmbedding p).val
        (hillPhysicalHminusEmbedding p).property =
      hillRealLabels p.val p.property.1 p.property.2 := by
  apply ordered_nat_enumeration_eq_of_multiplicity
  · exact finite_fiber_hillHminusRealLabels _ _
  · intro x
    exact (hillRealLabels_global_multiplicity p.val p.property.1 p.property.2 x).1
  · exact monotone_hillHminusRealLabels _ _
  · exact monotone_hillRealLabels p.val p.property.1 p.property.2
  · intro x
    rw [multiplicity_hillHminusRealLabels,
      (hillRealLabels_global_multiplicity p.val p.property.1 p.property.2 x).2,
      hillHminusRadicand_eq_physical]

end NLS.KdV
