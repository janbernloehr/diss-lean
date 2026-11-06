import NLS.KdV.HillSpectralCartesian
import NLS.KdV.HillAbelianCoordinateSequence
import NLS.KdV.HillUnitRealSourceUnembed

/-! # Exact original Abelian and real Cartesian normalizations

The complex Abelian coordinate uses sqrt(action); the Cartesian coordinate
uses sqrt(2*action). The literal full phases agree, including closed gaps,
and physical unembedding retains the original signed raw sequence.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV

theorem hillSpectralCartesian_eq_sqrt_two_mul_abelian (p : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1≤n) :
    hillSpectralCartesian p.val p.property.1 p.property.2 n hn=
      (Real.sqrt 2 : ℂ)*hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn := by
  rw [hillSpectralCartesian,hillDirichletAbelianCoordinate,Real.sqrt_mul (by norm_num : (0 : ℝ)≤2),ofReal_mul]
  unfold hillDirichletAbelianPhase hillDirichletCirclePhase
  ring

theorem hillAbelianRawCoordinateSequence_original_nat (p : RealPeriodOneHillPotential)
    (n : ℕ+) :
    hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) (n : ℤ)=
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
  have hn : 1≤(n : ℕ) := by have := n.pos; omega
  rw [hillAbelianRawCoordinateSequence,if_pos (by exact_mod_cast n.pos.le),Int.natAbs_natCast,
    hillAbelianPositiveCoefficient,dif_pos hn]
  exact congrArg (fun a : RealPeriodOneHillPotential =>
    hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos)
    (hillRealWeightedEmbedding_unitUnembed p)

theorem hillAbelianRawCoordinateSequence_original_neg (p : RealPeriodOneHillPotential)
    (n : ℕ+) :
    hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) (-(n : ℤ))=
      conj (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos) := by
  rw [hillAbelianRawCoordinateSequence_neg,hillAbelianRawCoordinateSequence_original_nat]

end NLS.KdV
