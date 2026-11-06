import NLS.KdV.HillOwnAmplitudeAnalytic
import NLS.KdV.HillEndpointSheetFacts
import NLS.KdV.HillDeflatedCanonicalRootPhase

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV

/-- Literal physical conjugation reverses only the signed sheet term
in the ORIGINAL own-gap Cartesian factor, including collapsed gaps. -/
theorem hillOwnGapFactor_conj
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    conj (hillOwnGapFactor q.val q.property.1 q.property.2 n n.pos) =
      2*((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos : ℂ)) -
      hillOwnGapFactor q.val q.property.1 q.property.2 n n.pos := by
  have hS : conj (hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)) =
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos) :=
    Complex.conj_eq_iff_im.mpr (hillDirichletSheetRoot_at_dirichlet_real q n n.pos)
  have hB : conj (hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 n
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)) =
      -hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 n
        (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos) := by
    have hRe := hillDeflatedEnergyCanonicalRoot_re_eq_zero_on_gap q.val q.property.1 q.property.2 n n.pos
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
      (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n n.pos)
    apply Complex.ext
    · simp only [conj_re,neg_re,hRe,neg_zero]
    · simp only [conj_im,neg_im]
  rw [hillOwnGapFactor,map_add,map_sub,conj_ofReal,conj_ofReal,map_div₀,hS,hB,div_neg]
  ring

theorem hillOwnCartesianAmplitude_conj
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    conj (hillOwnCartesianAmplitude q.val q.property.1 q.property.2 n n.pos) =
      hillActionGapPrefactor q.val q.property.1 q.property.2 n *
        (2*((hillRealGapCenter q.val q.property.1 q.property.2 n : ℂ)-
          (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos : ℂ)) -
          hillOwnGapFactor q.val q.property.1 q.property.2 n n.pos) := by
  rw [hillOwnCartesianAmplitude,map_mul,hillOwnGapFactor_conj]
  simp only [hillActionGapPrefactor,conj_ofReal]

end NLS.KdV
