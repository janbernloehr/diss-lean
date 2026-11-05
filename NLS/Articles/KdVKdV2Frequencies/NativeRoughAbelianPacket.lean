import NLS.Articles.KdVKdV2Frequencies.RoughAbelianNativeGerms
import NLS.KdV.HillPhysicalAbelianRoughContinuation

/-! # The actual native rough Abelian packet on one common source ball

ONE complex H-minus-one ball precedes every positive index. The Hilbert
output is the positive Sobolev-minus-one-half weighted original Abelian
coordinate. Every physical L2 source in the WHOLE rough ball is recovered,
including first and closed gaps, endpoint sheets and nonzero means.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

theorem exists_hillHminus_native_normalized_abelian_packet :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖Z q‖ ≤ C*‖q‖ ∧ ∀ j : ℤ, j≤0 → Z q j=0) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
            (Real.sqrt (1+(n : ℝ)) : ℂ) := by
  obtain ⟨η,C,Z,hη,hC,hZa,hZ0,hZb,hZp⟩ := exists_hillHminus_native_abelian_physical_germs
  refine ⟨η,C,Z,hη,hC,hZa,hZ0,hZb,?_⟩
  intro p hp n
  have hcoord : AnalyticOnNhd ℂ (fun q => Z q (n : ℤ)) (ball (0 : PeriodOneHminusOne) η) :=
    fun q hq => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (hZa q hq)
  exact hillDirichletAbelian_normalized_eq_on_rough_ball_of_germ zero_parity zero_real
    η hη n (fun q => Z q (n : ℤ)) hcoord (hZp n) p hp

end NLS.Articles.KdVKdV2Frequencies
