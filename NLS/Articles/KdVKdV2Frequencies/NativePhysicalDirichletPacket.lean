import NLS.Articles.KdVKdV2Frequencies.NativeRoughDirichletPacket
import NLS.KdV.HillHminusPhysicalDirichletNorming

/-! # A common rough analytic packet with the original physical normalization

The native H^-1 Hilbert maps restrict to the original physical L2 Dirichlet
energies and logarithmic multipliers, simultaneously at every positive index
on the same ball. This is matching spectral input for the rough Abelian map;
the full coordinate map and the main Birkhoff theorem remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_hillHminus_native_physical_dirichlet_packet :
    ∃ η C : ℝ, ∃ D K S : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧
      AnalyticOnNhd ℂ D (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ K (ball (0 : PeriodOneHminusOne) η) ∧
      AnalyticOnNhd ℂ S (ball (0 : PeriodOneHminusOne) η) ∧
      D 0 = 0 ∧ K 0 = 0 ∧ S 0 = 0 ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η,
        ‖D q‖+‖K q‖+‖S q‖ ≤ C*‖q‖ ∧
        (∀ n : ℕ+, hillHminusDirichlet q
          (((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*D q (n : ℤ)) = 0) ∧
        (∀ j : ℤ, j ≤ 0 → D q j = 0 ∧ K q j = 0 ∧ S q j = 0) ∧
        ∀ j : ℤ, S q j = sinh (K q j)) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
        ∀ n : ℕ+,
          D (hillPhysicalHminusEmbedding p).val (n : ℤ) =
            ((hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)-
              ((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) ∧
          K (hillPhysicalHminusEmbedding p).val (n : ℤ) =
            (hillDirichletLogMultiplier p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ) ∧
          S (hillPhysicalHminusEmbedding p).val (n : ℤ) =
            (Real.sinh (hillDirichletLogMultiplier p.val p.property.1 p.property.2
              (n : ℕ) n.property) : ℂ) := by
  obtain ⟨η,C,D,K,S,hη,hC,hDa,hKa,hSa,hD0,hK0,hS0,hall⟩ :=
    exists_hillHminus_native_dirichlet_packet
  refine ⟨η,C,D,K,S,hη,hC,hDa,hKa,hSa,hD0,hK0,hS0,?_,?_⟩
  · intro q hq
    obtain ⟨hb,hroot,_,hnonpos,hsinh⟩ := hall q hq
    exact ⟨hb,hroot,hnonpos,hsinh⟩
  · intro p hp n
    obtain ⟨hD,hK,hS⟩ := (hall _ hp).2.2.1 (hillPhysicalHminusEmbedding p).property n
    rw [hillHminusDirichletEnergy_eq_physical] at hD
    rw [hillHminusDirichletLogNorming_eq_physical] at hK hS
    exact ⟨hD,hK,hS⟩

end NLS.Articles.KdVKdV2Frequencies
