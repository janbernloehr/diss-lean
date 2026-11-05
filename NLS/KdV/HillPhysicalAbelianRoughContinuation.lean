import NLS.KdV.HillPhysicalRoughBallContinuation
import NLS.KdV.HillAbelianCoordinateAnalytic

/-! # Whole rough-ball recovery of the original physical Abelian coordinates -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem analyticAt_hillDirichletAbelianCoordinate_realScale
    (p : RealPeriodOneHillPotential) (n : ℕ+) (t : ℝ) :
    AnalyticAt ℝ (fun s => hillDirichletAbelianCoordinate (hillPhysicalRealScale p s).val
      (hillPhysicalRealScale p s).property.1 (hillPhysicalRealScale p s).property.2 n n.pos) t := by
  let q := hillPhysicalRealScale p t
  obtain ⟨Z,hZ,_hZ0,_hDZ,hmatch⟩ :=
    exists_hillDirichletAbelianCoordinate_analytic_extension q.val q.property.1 q.property.2 h0q h0r n n.pos
  let P : ℝ → Coeff 2 := fun s => SpectralWeight.one.toCoeff (hillPhysicalRealScale p s).val
  have hP : AnalyticAt ℝ P t := by
    let L : ℝ →L[ℝ] Coeff 2 :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (SpectralWeight.one.toCoeff p.val)
    have he : P=L := by
      funext s
      simp only [P,hillPhysicalRealScale,map_smul]
      rfl
    rw [he]
    exact L.analyticAt t
  have ha := hZ.restrictScalars (𝕜 := ℝ)
  have hlocal : AnalyticAt ℝ (fun s => Z (P s)) t := ha.comp (f := P) hP
  exact hlocal.congr ((continuous_hillPhysicalRealScale p).continuousAt.tendsto.eventually hmatch)

theorem hillDirichletAbelian_normalized_eq_on_rough_ball_of_germ
    (η : ℝ) (hη : 0<η) (n : ℕ+) (R : PeriodOneHminusOne → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η))
    (hgerm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val=
        hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
          (Real.sqrt (1+(n : ℝ)) : ℂ))
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η) :
    R (hillPhysicalHminusEmbedding p).val=
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
        (Real.sqrt (1+(n : ℝ)) : ℂ) :=
  hillPhysical_eq_on_rough_ball_of_scaling_germ η hη R hR
    (fun p => hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
      (Real.sqrt (1+(n : ℝ)) : ℂ))
    (fun p t => (analyticAt_hillDirichletAbelianCoordinate_realScale h0q h0r p n t).div_const)
    h0q h0r hgerm p hp

end NLS.KdV
