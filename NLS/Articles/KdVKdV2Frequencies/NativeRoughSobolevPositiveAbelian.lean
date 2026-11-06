import NLS.Articles.KdVKdV2Frequencies.RoughSobolevAbelianPacket
import NLS.Articles.KdVKdV2Frequencies.NativeRoughAbelianPacket
import NLS.KdV.HillRoughAbelianSquareComparison
import NLS.SequenceSpaces.WeightedAnalyticNormComparison

/-! # Stronger analyticity of the SAME actual positive rough Abelian map

One actual physical coordinate map and rough ball precede all orders and
real native sources. Actual physical square comparison is continued to the
WHOLE COMPLEX rough ball. Native complex norm bounds then prove weighted
sequence analyticity of the SAME original coordinate map, including closed
and low gaps, rather than only pointwise real-source membership.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem packet_norm_eq
    (η : ℝ) (hη : 0<η) (G Z : PeriodOneHminusOne → Coeff 2)
    (hGa : AnalyticOnNhd ℂ G (ball (0 : PeriodOneHminusOne) η))
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η))
    (hGzero : ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j≤0 → G q j=0)
    (hZzero : ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, j≤0 → Z q j=0)
    (hGphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
        (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0 →
      (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
        (hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos)^2/(1+(n : ℕ) : ℂ))
    (hZphys : ∀ p : RealPeriodOneHillPotential,
      (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
      Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/(Real.sqrt (1+(n : ℝ)) : ℂ)) :
    ∀ q∈ball (0 : PeriodOneHminusOne) η, ∀ j : ℤ, ‖G q j‖=‖Z q j‖ := by
  intro q hq j
  by_cases hj : 0<j
  · let n := Coeff.positivePoleIndex j hj
    have hn : (n : ℤ)=j := by exact_mod_cast Coeff.positivePoleIndex_real j hj
    have hf : AnalyticOnNhd ℂ (fun p => G p (n : ℤ)) (ball (0 : PeriodOneHminusOne) η) :=
      fun p hp => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (hGa p hp)
    have hg : AnalyticOnNhd ℂ (fun p => Z p (n : ℤ)) (ball (0 : PeriodOneHminusOne) η) :=
      fun p hp => ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (hZa p hp)
    have he (p : RealPeriodOneHillPotential)
        (hp : (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η)
        (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff p.val)
          (hillDirichletEnergy p.val p.property.1 p.property.2 n n.pos)≠0) :
        (G (hillPhysicalHminusEmbedding p).val (n : ℤ))^2=
          (Z (hillPhysicalHminusEmbedding p).val (n : ℤ))^2 := by
      have hsqrt : (Real.sqrt (1+(n : ℝ)) : ℂ)^2=(1+(n : ℕ) : ℂ) := by
        rw [←ofReal_pow,Real.sq_sqrt (by positivity),ofReal_add,ofReal_one,ofReal_natCast]
      rw [hGphys p hp n hw,hZphys p hp n,div_pow,hsqrt]
    have H := norm_eq_on_rough_ball_of_physical_abelian_sq η hη n
      (fun p => G p (n : ℤ)) (fun p => Z p (n : ℤ)) hf hg he q hq
    simpa only [hn] using H
  · rw [hGzero q hq j (by omega),hZzero q hq j (by omega)]

private theorem weighted_pullback_germ
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (U : Set P) (hU : IsOpen U)
    (Z G : P → Coeff 2) (hZa : AnalyticOnNhd ℂ Z U)
    (hmatch : ∀ p∈U, ∀ n : ℤ, ‖G p n‖=‖Z p n‖) (w : ℤ → ℂ)
    (q : E) (hq : L q∈U) (A : Set E) (hA : IsOpen A) (hqA : q∈A)
    (M : ℝ) (hM : 0≤M) (F : E → Coeff 2)
    (hdata : ∀ p∈A, ‖F p‖≤M ∧ ∀ n : ℤ, F p n=w n*G (L p) n) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ M : ℝ, 0≤M ∧
      AnalyticOnNhd ℂ (Coeff.weightedSequenceRealization w (fun p => Z (L p))) V ∧
      ∀ p∈V, L p∈U ∧ ‖Coeff.weightedSequenceRealization w (fun p => Z (L p)) p‖≤M ∧
        ∀ n : ℤ, Coeff.weightedSequenceRealization w (fun p => Z (L p)) p n=w n*Z (L p) n := by
  let V : Set E := A∩L ⁻¹' U
  have hV : IsOpen V := hA.inter (hU.preimage L.continuous)
  obtain ⟨ha,hvalues⟩ := Coeff.analytic_weightedSequenceRealization_of_complex_norm_comparison
    L U Z hZa w V hV (fun _ hp => hp.2) F M (fun p hp => (hdata p hp.1).1) (by
      intro p hp n
      rw [(hdata p hp.1).2 n,norm_mul,norm_mul,hmatch (L p) hp.2 n])
  exact ⟨V,hV,⟨hqA,hq⟩,M,hM,ha,fun p hp => ⟨hp.2,hvalues p hp⟩⟩

/-- ONE ACTUAL original positive rough Abelian map is complex analytic in
EVERY stronger native Sobolev sequence norm near EVERY eligible real source
in ONE common rough ball. Exact physical recovery and weak zero/linear
bounds are retained for the SAME map, before all orders and sources. -/
theorem exists_hillHminus_actual_all_sobolev_positive_abelian :
    ∃ η C : ℝ, ∃ Z : PeriodOneHminusOne → Coeff 2,
      0<η ∧ 0<C ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) η, ‖Z q‖≤C*‖q‖ ∧ ∀ j : ℤ, j≤0 → Z q j=0) ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ n : ℕ+,
        Z (hillPhysicalHminusEmbedding p).val (n : ℤ)=
          hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
            (Real.sqrt (1+(n : ℝ)) : ℂ)) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) η →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ M : ℝ, 0≤M ∧
            AnalyticOnNhd ℂ (Coeff.weightedSequenceRealization
              (fun n => (Weight.sobolev t n : ℂ)) (fun p => Z (periodOneSobolevImageInclusion t ht p))) V ∧
            ∀ p∈V, periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧
              ‖Coeff.weightedSequenceRealization (fun n => (Weight.sobolev t n : ℂ))
                (fun p => Z (periodOneSobolevImageInclusion t ht p)) p‖≤M ∧
              ∀ n : ℤ, Coeff.weightedSequenceRealization (fun n => (Weight.sobolev t n : ℂ))
                (fun p => Z (periodOneSobolevImageInclusion t ht p)) p n=
                  (Weight.sobolev t n : ℂ)*Z (periodOneSobolevImageInclusion t ht p) n := by
  obtain ⟨rG,_CG,G,hrG,_hCG,hGa,hGb,hGphys,hstrong⟩ :=
    exists_hillHminus_all_sobolev_abelian_squared_packet
  obtain ⟨rZ,C,Z,hrZ,hC,hZa,hZ0,hZb,hZphys⟩ := exists_hillHminus_native_normalized_abelian_packet
  let η := min rG rZ
  have hη : 0<η := lt_min hrG hrZ
  have hsubG : ball (0 : PeriodOneHminusOne) η⊆ball (0 : PeriodOneHminusOne) rG :=
    ball_subset_ball (min_le_left _ _)
  have hsubZ : ball (0 : PeriodOneHminusOne) η⊆ball (0 : PeriodOneHminusOne) rZ :=
    ball_subset_ball (min_le_right _ _)
  have hmatch := packet_norm_eq η hη G Z (hGa.mono hsubG) (hZa.mono hsubZ)
    (fun q hq => (hGb q (hsubG hq)).2) (fun q hq => (hZb q (hsubZ hq)).2)
    (fun p hp n hw => hGphys p (hsubG hp) n hw) (fun p hp n => hZphys p (hsubZ hp) n)
  refine ⟨η,C,Z,hη,hC,hZa.mono hsubZ,hZ0,(fun q hq => hZb q (hsubZ hq)),
    (fun p hp n => hZphys p (hsubZ hp) n),?_⟩
  intro t ht q hreal hq
  obtain ⟨U,hU,hqU,M,F,hM,_hFa,hdata⟩ := hstrong t ht q hreal (hsubG hq)
  exact weighted_pullback_germ (periodOneSobolevImageInclusion t ht)
    (ball (0 : PeriodOneHminusOne) η) isOpen_ball Z G (hZa.mono hsubZ) hmatch
    (fun n => (Weight.sobolev t n : ℂ)) q hq U hU hqU M hM F
    (fun p hp => (hdata p hp).2)

end NLS.Articles.KdVKdV2Frequencies
