import NLS.ZakharovShabat.SourceStandardRootAnalytic

/-!
# Joint analyticity of source periodic standard roots

The normalized principal root is analytic in both spectral parameter and
source coefficients wherever the spectral point avoids the moving closed
gap segment. The same connected almost-real source domain from Lemma 10.2
works for all periodic indices.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Composition of analytic midpoint and squared-gap data with the
principal-root branch gives joint analyticity off its cut. -/
theorem normalizedStandardRoot_joint_analyticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M G : E → ℂ) (ψ : E) (z : ℂ)
    (hMid : AnalyticAt ℂ M ψ) (hGap : AnalyticAt ℂ G ψ)
    (hz : M ψ ≠ z)
    (hslit : 1-G ψ/(4*(M ψ-z)^2) ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun t : ℂ × E => normalizedStandardRoot (M t.2) (G t.2) t.1) (z,ψ) := by
  have hMidJoint : AnalyticAt ℂ (fun t : ℂ × E => M t.2) (z,ψ) :=
    hMid.comp (analyticAt_snd (p := (z,ψ)))
  have hGapJoint : AnalyticAt ℂ (fun t : ℂ × E => G t.2) (z,ψ) :=
    hGap.comp (analyticAt_snd (p := (z,ψ)))
  have hlin : AnalyticAt ℂ (fun t : ℂ × E => M t.2-t.1) (z,ψ) :=
    hMidJoint.sub analyticAt_fst
  have hden0 : (4:ℂ)*(M ψ-z)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hz))
  have hden : AnalyticAt ℂ (fun t : ℂ × E => 4*(M t.2-t.1)^2) (z,ψ) :=
    analyticAt_const.mul (hlin.pow 2)
  have hrad : AnalyticAt ℂ
      (fun t : ℂ × E => 1-G t.2/(4*(M t.2-t.1)^2)) (z,ψ) :=
    analyticAt_const.sub (hGapJoint.div hden hden0)
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1-G ψ/(4*(M ψ-z)^2)) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hcomp0 := hsqrt.comp
    (f := fun t : ℂ × E => 1-G t.2/(4*(M t.2-t.1)^2)) hrad
  have hcomp : AnalyticAt ℂ
      (fun t : ℂ × E => Complex.sqrt (1-G t.2/(4*(M t.2-t.1)^2))) (z,ψ) := by
    simpa only [Function.comp_def] using hcomp0
  have heq : (fun t : ℂ × E => normalizedStandardRoot (M t.2) (G t.2) t.1) =
      (fun t : ℂ × E => M t.2-t.1) *
      (fun t : ℂ × E => Complex.sqrt (1-G t.2/(4*(M t.2-t.1)^2))) := by
    funext t
    rfl
  rw [heq]
  exact hlin.mul hcomp

/-- Joint analyticity of the canonical source root from analytic symmetric
periodic spectral data. -/
theorem sourceStandardRoot_joint_analyticAt_of_symmetric
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hMid : AnalyticAt ℂ (fun χ : CoeffPair p =>
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ)
    (hGap : AnalyticAt ℂ (fun χ : CoeffPair p =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2) ψ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (fun t : ℂ × CoeffPair p => sourceStandardRoot hp hp1 t.2 n t.1) (z,ψ) := by
  let M : CoeffPair p → ℂ := fun χ =>
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n
  let G : CoeffPair p → ℂ := fun χ =>
    (canonicalPeriodicGap hp hp1 (periodOnePotential χ) (periodOnePotential_mem χ) n)^2
  have hnonzero : M ψ ≠ z := by
    intro he
    exact hz (he.symm ▸ sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)
  have hslit : 1-G ψ/(4*(M ψ-z)^2) ∈ Complex.slitPlane :=
    sourceStandardRoot_radicand_mem_slitPlane hp hp1 ψ n z hz
  have h := normalizedStandardRoot_joint_analyticAt M G ψ z hMid hGap hnonzero hslit
  exact h

/-- On one connected almost-real source domain, every indexed standard
root is jointly analytic outside its moving gap segment. -/
theorem exists_global_source_analytic_standardRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ, ∀ z : ℂ,
        z ∉ sourcePeriodicSegment hp hp1 ψ n →
        AnalyticAt ℂ (fun t : ℂ × CoeffPair p =>
          sourceStandardRoot hp hp1 t.2 n t.1) (z,ψ) := by
  obtain ⟨W, hWopen, hWconnected, hR, hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro ψ hψ n z hz
  obtain ⟨hMid, hGap⟩ := hA ψ hψ n
  exact sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 ψ n z hMid hGap hz

/-- Analytic-on-a-neighborhood form of the joint standard-root theorem. -/
theorem exists_global_source_analyticOnNhd_standardRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧ ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceStandardRoot hp hp1 t.2 n t.1)
          {t | t.2 ∈ W ∧ t.1 ∉ sourcePeriodicSegment hp hp1 t.2 n} := by
  obtain ⟨W, hWopen, hWconnected, hR, hA⟩ :=
    exists_global_source_analytic_standardRoot hp hp1
  refine ⟨W, hWopen, hWconnected, hR, ?_⟩
  intro n t ht
  exact hA t.2 ht.1 n t.1 ht.2

end NLS.ZakharovShabat
