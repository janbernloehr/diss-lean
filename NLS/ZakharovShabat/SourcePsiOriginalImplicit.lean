import NLS.ZakharovShabat.SourcePsiOriginalRealSolution
import NLS.ZakharovShabat.SourcePsiOriginalJacobianInverse
import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-!
# Analytic implicit branches of the original equation

The real equation is jointly analytic on the real source and root
Banach spaces. The actual complex root derivative and Corollary 12.8
give an analytic local branch through every original-domain zero.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint analyticity on the real source and deleted root spaces. -/
theorem SourceLemma12_4Data.originalRealEquation_joint_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℝ
      (fun t : realTypeSourceSubmodule p × RealDeletedCoeff p n => sourcePsiOriginalRealEquation hp hp1 n t.2 t.1)
      {t | (t.1:CoeffPair p) ∈ W} := by
  intro t ht
  let L : realTypeSourceSubmodule p × RealDeletedCoeff p n →L[ℝ] CoeffPair p × DeletedCoeff p n :=
    (realTypeSourceSubmodule p).subtypeL.prodMap (RealDeletedCoeff.complexCLM n)
  exact ((RealDeletedCoeff.reCLM n).analyticAt _).comp
    ((H.real_analytic n (L t) ⟨ht,mem_univ _⟩).comp (L.analyticAt t))

/-- Apply the analytic implicit function theorem to the actual original equation. -/
theorem SourceLemma12_7Data.originalEquation_local_analytic_branch
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_7Data hp hp1 W) (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (t : realTypeSourceSubmodule p × RealCoeff p)
    (htW : (t.1:CoeffPair p) ∈ W) (htΩ : t ∈ sourcePsiOriginalOmega V D) (n : ℤ)
    (hz : sourcePsiOriginalEquation hp hp1 n
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1 = 0) :
    ∃ s : CoeffPair p → DeletedCoeff p n, AnalyticAt ℂ s (t.1:CoeffPair p) ∧
      s t.1 = Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2) ∧
      ∀ᶠ ψ in 𝓝 (t.1:CoeffPair p), sourcePsiOriginalEquation hp hp1 n (s ψ) ψ = 0 := by
  let a := Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun u => sourcePsiOriginalEquation hp hp1 n u.1 u.2
  have hswap : AnalyticAt ℂ
      (fun u : DeletedCoeff p n × CoeffPair p => (u.2,u.1)) (a,(t.1:CoeffPair p)) :=
    analyticAt_snd.prod analyticAt_fst
  have hF : AnalyticAt ℂ F (a,(t.1:CoeffPair p)) := by
    exact (H.previous.previous.previous.analytic n ((t.1:CoeffPair p),a) ⟨htW,mem_univ _⟩).comp
      (f := fun u : DeletedCoeff p n × CoeffPair p => (u.2,u.1)) hswap
  have hinc : HasFDerivAt (fun b : DeletedCoeff p n => (b,(t.1:CoeffPair p)))
      (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) a :=
    hasFDerivAt_prodMk_left a (t.1:CoeffPair p)
  have hpartial : (fderiv ℂ F (a,(t.1:CoeffPair p))).comp
      (ContinuousLinearMap.inl ℂ (DeletedCoeff p n) (CoeffPair p)) =
      sourcePsiOriginalRootJacobian hp hp1 n a t.1 :=
    (hF.differentiableAt.hasFDerivAt.comp a hinc).fderiv.symm
  apply NLS.ComplexAnalysis.exists_analytic_implicitBanachRoot F a (t.1:CoeffPair p) hF hz
  rw [hpartial]
  exact H.originalJacobian_bijective hD hV t htW htΩ n

/-- Every placed real zero extends through the canonical analytic branch,
which stays in the same original deleted domain on nearby real sources. -/
theorem SourceLemma12_4Data.originalRealEquation_local_real_branch
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (a : RealDeletedCoeff p n)
    (ht : (φ,a) ∈ sourcePsiOriginalDeletedOmega V D n)
    (hz : sourcePsiOriginalRealEquation hp hp1 n a φ = 0) :
    ∃ s : realTypeSourceSubmodule p → RealDeletedCoeff p n,
      AnalyticAt ℝ s φ ∧ s φ = a ∧
      ∀ᶠ ψ in 𝓝 φ, (ψ,s ψ) ∈ sourcePsiOriginalDeletedOmega V D n ∧
        sourcePsiOriginalRealEquation hp hp1 n (s ψ) ψ = 0 := by
  refine ⟨sourcePsiOriginalRootReal hp hp1 n,
    analyticOnNhd_sourcePsiOriginalRootReal hp hp1 n φ (mem_univ _),?_,?_⟩
  · exact (H.originalRealEquation_zero_unique hD φ (hR φ.property) ht.1 n a ht.2 hz).symm
  · have hnear : ∀ᶠ ψ : realTypeSourceSubmodule p in 𝓝 φ, (ψ:CoeffPair p) ∈ V :=
      continuous_subtype_val.continuousAt.eventually (hV.mem_nhds ht.1)
    filter_upwards [hnear] with ψ hψ
    exact ⟨hD.originalRootReal_graph ψ hψ n,H.originalRootReal_solves hW hR n ψ⟩

end NLS.ZakharovShabat
