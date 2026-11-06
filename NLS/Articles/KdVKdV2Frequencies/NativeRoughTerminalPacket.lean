import NLS.Articles.KdVKdV2Frequencies.NativeRoughDivisorPacket
import NLS.KdV.HillHminusDirichletInverseSequence
import NLS.KdV.HillPhysicalRoughBallContinuation
import NLS.KdV.HillHminusPhysicalDirichletNorming

/-! # The actual normalized rough Dirichlet terminal in its native Hilbert norm

One complex rough ball precedes every index. The original physical
terminal factor divided by n is recovered throughout that whole ball,
including closed gaps and sources whose L2 norm is large.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by simp
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff
    (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by intro j; simp

theorem exists_hillHminus_native_normalized_terminal_packet :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → Coeff 2,
      0 < η ∧ 0 < C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖Z q‖ ≤ C*‖q‖ ∧ ∀ j : ℤ, j ≤ 0 → Z q j=0) ∧
      ∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 (n : ℕ) n.property/(n : ℂ) := by
  obtain ⟨rD,CD,T,A,K,S,hrD,_hCD,hTa,hAa,_hKa,hSa,hT0,hA0,_hK0,hS0,hdata⟩ :=
    exists_hillHminus_native_divisor_packet
  have hactual (p : RealPeriodOneHillPotential)
      (hp : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) rD) (n : ℕ+) :
      T (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        ((hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ)-
          ((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) ∧
      A (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        ((hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ)-
          (hillRealGapCenter p.val p.property.1 p.property.2 (n : ℕ) : ℂ))/(n : ℂ) ∧
      S (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        (Real.sinh (hillDirichletLogMultiplier p.val p.property.1 p.property.2 (n : ℕ) n.property) : ℂ) := by
    obtain ⟨ht,ha,_hk,hs⟩ := (hdata _ hp).2.2.1 (hillPhysicalHminusEmbedding p).property n
    rw [hillHminusGapMidpoint_eq_physical] at ht ha
    rw [hillHminusDirichletEnergy_eq_physical] at ha
    rw [hillHminusDirichletLogNorming_eq_physical] at hs
    exact ⟨ht,ha,hs⟩
  let D : PeriodOneHminusOne → Coeff 2 := fun q => A q+T q
  have hDa : AnalyticAt ℂ D 0 := (hAa 0 (mem_ball_self hrD)).add (hTa 0 (mem_ball_self hrD))
  have hD0 : D 0=0 := by simp only [D,hA0,hT0,zero_add]
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,map_zero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto
        (⟨0,zero_parity,zero_real⟩ : RealPeriodOneHillPotential)
  have hnear : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) rD :=
    ht.eventually (ball_mem_nhds (0 : PeriodOneHminusOne) hrD)
  have hDphysical (n : ℕ+) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      hillHminusMovingDirichletEnergy D n (hillPhysicalHminusEmbedding p).val=
        (hillDirichletEnergy p.val p.property.1 p.property.2 (n : ℕ) n.property : ℂ) := by
    filter_upwards [hnear] with p hp
    obtain ⟨hTp,hAp,_⟩ := hactual p hp n
    change ((Real.pi : ℂ)*(n : ℕ))^2+(n : ℂ)*
      (A (hillPhysicalHminusEmbedding p).val (n : ℤ)+T (hillPhysicalHminusEmbedding p).val (n : ℤ))=_
    rw [hTp,hAp]
    have hnn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
    have halg (c m a k : ℂ) (hk : k≠0) : c+k*((m-a)/k+(a-c)/k)=m := by field_simp; ring
    exact halg _ _ _ _ hnn
  obtain ⟨rH,CH,H,hrH,_hCH,hHa,_hHb,hHphysical⟩ :=
    exists_hillHminus_native_moving_root_inverse zero_parity zero_real D hDa hD0 hDphysical
  let B : Coeff ⊤ →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 := Coeff.holderProduct
  let L : Coeff 2 →L[ℂ] Coeff 2 := (4 : ℂ) • Coeff.multiplierCLM hillPositiveHalfSign
  let Z : PeriodOneHminusOne → Coeff 2 := fun q => L (B (H q) (S q))-A q
  let r : ℝ := min rD rH
  have hr : 0 < r := lt_min hrD hrH
  have hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) r) := by
    intro q hq
    have hs := hSa q (ball_subset_ball (min_le_left rD rH) hq)
    have hh := hHa q (ball_subset_ball (min_le_right rD rH) hq)
    have hb := (B.analyticAt_bilinear _).comp₂ hh hs
    exact ((L.analyticAt _).comp (f := fun q => B (H q) (S q)) hb).sub
      (hAa q (ball_subset_ball (min_le_left rD rH) hq))
  have hZ0 : Z 0=0 := by simp only [Z,hS0,map_zero,hA0,sub_self]
  have hZval (q : PeriodOneHminusOne) (j : ℤ) :
      Z q j=(4 : ℂ)*hillPositiveHalfSign j*(H q j*S q j)-A q j := by
    change (4 : ℂ)*(hillPositiveHalfSign j*(H q j*S q j))-A q j=_
    ring
  have hZpos (q : PeriodOneHminusOne) (n : ℕ+) :
      Z q (n : ℤ)=2*(-1 : ℂ)^(n : ℕ)*H q (n : ℤ)*S q (n : ℤ)-A q (n : ℤ) := by
    rw [hZval]
    simp only [hillPositiveHalfSign,if_pos (show (0 : ℤ) < (n : ℤ) by exact_mod_cast n.property),
      Int.natAbs_natCast]
    ring
  have hgerm (n : ℕ+) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,zero_parity,zero_real⟩,
      Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianTerminalFactor p.val p.property.1 p.property.2 (n : ℕ) n.property/(n : ℂ) := by
    filter_upwards [hnear,hHphysical n] with p hp hpH
    obtain ⟨_hTp,hAp,hSp⟩ := hactual p hp n
    rw [hZpos,hpH,hAp,hSp]
    dsimp only [hillDirichletAbelianTerminalFactor]
    have hsheet := hillDirichletSheetRoot_at_dirichlet_eq_norming p.val p.property.1 p.property.2
      (n : ℕ) n.property
    rw [hsheet]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  obtain ⟨s,C,hs,hC,hsZa,hZbound⟩ := exists_analytic_zero_linear_bound Z (hZa 0 (mem_ball_self hr)) hZ0
  let η : ℝ := min r s
  have hη : 0 < η := lt_min hr hs
  have hηD : η ≤ rD := (min_le_left r s).trans (min_le_left rD rH)
  have hηZa := hsZa.mono (ball_subset_ball (min_le_right r s))
  refine ⟨η,C,Z,hη,hC,hηZa,hZ0,?_,?_⟩
  · intro q hq
    refine ⟨hZbound q (ball_subset_ball (min_le_right r s) hq),?_⟩
    intro j hj
    have hAj := ((hdata q (ball_subset_ball hηD hq)).2.2.2.1 j hj).2.1
    rw [hZval]
    simp only [hillPositiveHalfSign,if_neg (not_lt.mpr hj),mul_zero,zero_mul,hAj,sub_self]
  · intro p hp n
    have hcoord : AnalyticOnNhd ℂ (fun q => Z q (n : ℤ)) (ball (0 : PeriodOneHminusOne) η) := by
      intro q hq
      exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt (Z q)).comp (hηZa q hq)
    exact hillDirichletTerminal_normalized_eq_on_rough_ball_of_germ η hη n
      (fun q => Z q (n : ℤ)) hcoord zero_parity zero_real (hgerm n) p hp

end NLS.Articles.KdVKdV2Frequencies
