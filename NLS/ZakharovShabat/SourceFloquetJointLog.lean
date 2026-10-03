import NLS.ComplexAnalysis.NormalizedLogChart
import NLS.ZakharovShabat.SourceFloquetMultiplier

/-! # Joint Floquet logarithms and their exact differential

On the joint moving-cut complement, a normalized local logarithm has
joint differential `d Delta / canonicalRoot`. This holds at complex
sources throughout the analytic source domain, not just at real ones.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceFloquetJointMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p) : ℂ × CoeffPair p → ℂ :=
  fun t => sourceFloquetMultiplier hp hp1 t.2 t.1

theorem sourceFloquetJointMultiplier_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W)) :
    AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) := by
  intro t ht
  exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t (mem_univ t)).add (hroot t ht)).div_const

/-- One open complex-source domain containing every real source
supports both the root and the multiplier as jointly analytic maps. -/
theorem exists_global_source_analytic_floquetMultiplier
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) ∧
      AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W) := by
  obtain ⟨W,hW,hconn,hreal,hD,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  exact ⟨W,hW,hconn,hreal,hD,hroot,sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot⟩

/-- The full joint differential of a local Floquet logarithm. Its
restriction to source directions is the gradient in Lemma 19.1(i). -/
theorem normalizedLogChart_sourceFloquet_hasFDerivAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (a t : ℂ × CoeffPair p) (A : ℂ)
    (ha : a ∈ sourceCanonicalRootJointDomain hp hp1 W)
    (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 W)
    (hlog : sourceFloquetJointMultiplier hp hp1 t / sourceFloquetJointMultiplier hp hp1 a ∈ slitPlane) :
    HasFDerivAt (normalizedLogChart (sourceFloquetJointMultiplier hp hp1) a A)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  let Δ : ℂ × CoeffPair p → ℂ := fun u => canonicalDiscriminant hp (periodOnePotential u.2) u.1
  let Q := sourceCanonicalRootJointProduct hp hp1
  let M := sourceFloquetJointMultiplier hp hp1
  have hΔ : DifferentiableAt ℂ Δ t := (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t (mem_univ t)).differentiableAt
  have hQ : DifferentiableAt ℂ Q t := (hroot t ht).differentiableAt
  have hM : HasFDerivAt M ((2:ℂ)⁻¹ • (fderiv ℂ Δ t + fderiv ℂ Q t)) t := by
    convert! (hΔ.hasFDerivAt.add hQ.hasFDerivAt).const_smul (2:ℂ)⁻¹ using 1
    funext u
    change (Δ u+Q u)/2 = (2:ℂ)⁻¹*(Δ u+Q u)
    rw [div_eq_inv_mul]
  have hqne : Q t ≠ 0 := sourceCanonicalRoot_ne_zero_off_gaps hp hp1 t.2 t.1 ht.2
  have hmne : M t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2
  have hane : M a ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 a.2 a.1 ha.2
  have hqder (v : ℂ × CoeffPair p) : (fderiv ℂ Q t) v = Δ t/Q t*(fderiv ℂ Δ t) v :=
    fderiv_squareRoot_of_sq_eq_discriminant_sq_sub_four Q Δ _ hD
      (fun u hu => sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 u.2 u.1 hu.2)
      t ht hQ hΔ hqne v
  have h := normalizedLogChart_hasFDerivAt M a t A hane hM.differentiableAt hlog
  rw [hM.fderiv] at h
  have he : (Q t)⁻¹ • fderiv ℂ Δ t =
      (M t)⁻¹ • ((2:ℂ)⁻¹ • (fderiv ℂ Δ t + fderiv ℂ Q t)) := by
    apply ContinuousLinearMap.ext
    intro v
    change (Q t)⁻¹ * (fderiv ℂ Δ t) v = (M t)⁻¹ * ((2:ℂ)⁻¹ *
      ((fderiv ℂ Δ t) v + (fderiv ℂ Q t) v))
    rw [hqder v]
    field_simp
    dsimp [M,sourceFloquetJointMultiplier,sourceFloquetMultiplier,Q,sourceCanonicalRootJointProduct,Δ]
    ring
  rw [← he] at h
  exact h

end NLS.ZakharovShabat
