import NLS.KdV.HillRoughAbelianConstantSign
import NLS.KdV.HillAbelianCoordinateSequence
import NLS.SequenceSpaces.ConstantSignPacketTransport

/-! # Exact physical signs of the SAME actual positive Abelian map

Original physical recovery and square agreement off the actual Dirichlet
sheet fix ONE infinite sign selection on the WHOLE common complex rough
ball. The choice precedes all sources and stronger Sobolev orders.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The supplied physical positive map is EXACTLY one fixed sign change
of the actual squared packet, throughout the common complex rough ball. -/
theorem exists_constant_signChange_positive_rough_packet
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
    ∃ e : ℤ → Bool, ∀ q∈ball (0 : PeriodOneHminusOne) η, Z q=Coeff.signChange e (G q) := by
  apply Coeff.exists_constant_signChange_of_eqOn_or_neg
  intro j
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
    have H := eqOn_or_neg_rough_ball_of_physical_abelian_sq η hη n
      (fun p => Z p (n : ℤ)) (fun p => G p (n : ℤ)) hg hf
      (fun p hp hw => (he p hp hw).symm)
    simpa only [EqOn,hn] using H
  · exact Or.inl (fun q hq => by rw [hZzero q hq j (by omega),hGzero q hq j (by omega)])

end NLS.KdV
