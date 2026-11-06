import NLS.MKdV.MiuraSupportedAbelianTraceContraction
import NLS.MKdV.MiuraDirichletContourExclusion
import NLS.ZakharovShabat.SourceCriticalRootRatioContourHomotopy

/-! # Actual Abelian contraction on the original physical action circles

The actual trace kernels are analytic off the original periodic cuts.
Finite circle-integral exchange and the supported interpolation reduce
the original Dirichlet action generators to the normalized Abelian
frequency-circle period, with its positive factor one over pi.
-/
noncomputable section
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraDirichletTraceKernel (a : ScalarDomain 2) (ha : ∀ j,a.val j = conj (a.val (-j)))
    (m : ℕ) (hm : 1 ≤ m) (z : ℂ) : ℂ :=
  z*(∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve (realSobolevMiuraHillPotential a ha) m hm) x*
    extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) (z^2)) x)/
      sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z

theorem analyticAt_miuraDirichletTraceKernel (a : ScalarDomain 2)
    (ha : ∀ j,a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))) :
    AnalyticAt ℂ (miuraDirichletTraceKernel a ha m hm) z := by
  let q := realSobolevMiuraHillPotential a ha
  let μ : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 m hm
  let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
  let D := deriv s μ
  let S := hillDirichletSheetRoot (sobolevMiuraHillPotential a) μ
  let R := sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a))
  let H (w : ℂ) := w*(S*s (w^2)/(2*(μ-w^2)*D))/R w
  have hD : D ≠ 0 := by
    dsimp only [D,s]
    rw [← realSobolevMiuraHillPotential_toCoeff a ha]
    exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 μ
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 m hm)
  have hμ : μ-z^2 ≠ 0 := sub_ne_zero.mpr (miuraDirichletEnergy_ne_sq_on_rootDomain a ha m hm z hz).symm
  have hs : AnalyticAt ℂ (fun w : ℂ => s (w^2)) z :=
    (analyticOnNhd_hillL2DirichletCharacteristic _ _ (mem_univ _)).comp (analyticAt_id.pow 2)
  have hden : AnalyticAt ℂ (fun w : ℂ => 2*(μ-w^2)*D) z :=
    (analyticAt_const.mul (analyticAt_const.sub (analyticAt_id.pow 2))).mul analyticAt_const
  have hroot : AnalyticAt ℂ R z := sourceCanonicalRoot_analyticOnNhd (by simp) (by norm_num) _ z hz
  have hA : AnalyticAt ℂ H z :=
    (analyticAt_id.mul ((analyticAt_const.mul hs).div hden
      (mul_ne_zero (mul_ne_zero (by norm_num) hμ) hD))).div hroot
        (sourceCanonicalRoot_ne_zero_off_gaps (by simp) (by norm_num) _ z hz)
  have he : miuraDirichletTraceKernel a ha m hm =ᶠ[𝓝 z] H := by
    filter_upwards [(isOpen_sourceCanonicalRootDomain_of_realType (by simp) (by norm_num) _
      (realDiagonalH1Source a ha).property).mem_nhds hz] with w hw
    have hr := integral_hillDirichletGradient_discriminantSpatial_sheet_resolvent q m hm (w^2)
      (miuraDirichletEnergy_ne_sq_on_rootDomain a ha m hm w hw).symm
    dsimp only at hr
    simp only [q,realSobolevMiuraHillPotential_toCoeff a ha] at hr
    exact congrArg (fun v : ℂ => w*v/R w) hr
  exact hA.congr he.symm

theorem miuraSupportedAbelian_original_action_circle_contraction (a : ScalarDomain 2)
    (ha : ∀ j,a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (hsheet : ∀ k ∈ F,hillDirichletSheetRoot (sobolevMiuraHillPotential a)
      (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k) ≠ 0)
    (c : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hcircle : sphere c ρ ⊆ sourceCanonicalRootDomain (by simp) (by norm_num) (sobolevSourceInclusion (a,a))) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    (∑ k ∈ F,ψ (hillDirichletEnergies q k)*
      (-(2/(Real.pi : ℂ))*(∮ z in C(c,ρ),miuraDirichletTraceKernel a ha (k+1) (by omega) z))/
        hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)) =
      (1/(Real.pi : ℂ))*(∮ z in C(c,ρ),z*ψ (z^2)/
        sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a)) z) := by
  let q := realSobolevMiuraHillPotential a ha
  let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
  let R := sourceCanonicalRoot (by simp) (by norm_num) (sobolevSourceInclusion (a,a))
  let W (k : ℕ) := ψ (hillDirichletEnergies q k)/
    hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)
  have hint (k : ℕ) (_ : k ∈ F) : CircleIntegrable (fun z => W k*miuraDirichletTraceKernel a ha (k+1) (by omega) z) c ρ := by
    apply ContinuousOn.circleIntegrable hρ
    intro z hz
    exact (analyticAt_const.mul (analyticAt_miuraDirichletTraceKernel a ha (k+1) (by omega) z (hcircle hz))).continuousAt.continuousWithinAt
  have hpoint (z : ℂ) (hz : z ∈ sphere c ρ) :
      (∑ k ∈ F,W k*miuraDirichletTraceKernel a ha (k+1) (by omega) z) = -(1/2 : ℂ)*(z*ψ (z^2)/R z) := by
    have hc := miuraSelectedAbelianPsi_supported_trace_contraction a ha n hn F hnF hclosed hsheet (z^2)
      (fun k _ => miuraDirichletEnergy_ne_sq_on_rootDomain a ha (k+1) (by omega) z (hcircle hz))
    calc
      _ = z/R z*(∑ k ∈ F,ψ (hillDirichletEnergies q k)*
          (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q (k+1) (by omega)) x*
            extend (hillEnergyTraceGradientSpatialCurve (sobolevMiuraHillPotential a) (z^2)) x)/
              hillDirichletSheetRoot (sobolevMiuraHillPotential a) (hillDirichletEnergies q k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        dsimp only [W,miuraDirichletTraceKernel,R]
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [hc];ring
  calc
    _ = -(2/(Real.pi : ℂ))*(∑ k ∈ F,W k*(∮ z in C(c,ρ),miuraDirichletTraceKernel a ha (k+1) (by omega) z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [W]
      ring
    _ = -(2/(Real.pi : ℂ))*(∮ z in C(c,ρ),∑ k ∈ F,W k*miuraDirichletTraceKernel a ha (k+1) (by omega) z) := by
      rw [circleIntegral.integral_fun_sum hint]
      simp only [circleIntegral.integral_const_mul]
    _ = -(2/(Real.pi : ℂ))*(∮ z in C(c,ρ),-(1/2 : ℂ)*(z*ψ (z^2)/R z)) := by
      congr 1
      exact circleIntegral.integral_congr hρ hpoint
    _ = _ := by rw [circleIntegral.integral_const_mul];ring

end NLS.MKdV
