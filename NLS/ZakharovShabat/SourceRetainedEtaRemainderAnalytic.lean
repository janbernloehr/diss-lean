import NLS.ZakharovShabat.SourceEtaRemainderLocalGapBound

/-! Scalar analyticity of the SAME actual own-index eta remainders on
ONE complex source neighborhood before ALL labels, including closed gaps.
Only the retained original annulus and root data are used. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_ownEtaRemainder_common_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p),IsOpen U ∧ φ.val∈U ∧ U⊆W ∧
      ∀ n : ℤ,AnalyticOnNhd ℂ (sourceAngularEtaRemainder hp hp1 n s) U := by
  obtain ⟨a,ha,_,_,_,_,hball,_⟩ := D.angular.psi.isolation φ
  let O := W∩ball φ.val a
  have hO : IsOpen O := D.source_open.inter isOpen_ball
  have hφO : φ.val∈O := ⟨D.real_subset φ.property,mem_ball_self ha⟩
  have hOW₀ : O⊆W₀ := fun _ h => hball h.2
  have hOB : O⊆B := fun _ h => D.source_subset h.1
  obtain ⟨V,hV,hφV,hVO,hcharts⟩ :=
    D.angular.psi.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_allIndices
      O hO hOW₀ (fun ψ hψ => D.angular.symmetric_analytic ψ (hOB hψ)) φ.val hφO φ.property
  refine ⟨V,hV,hφV,(fun _ h => (hVO h).1),?_⟩
  intro n
  obtain ⟨c,T,r,R,z₀,C⟩ := hcharts n
  exact C.analyticOnNhd_etaRemainder ((r+R)/2) (by linarith [C.inner_lt_outer])
    (by linarith [C.inner_lt_outer]) ((D.angular.roots_analytic .dirichlet n).mono (hVO.trans hOB))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
