import NLS.KdV.HminusOneCanonicalDirichletMultiplicity
import NLS.KdV.HminusOneDirichletUniformDisplacement
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic

/-! # Original asymptotics of the analytic Dirichlet divisor

The intrinsic complex high labels agree with the analytic divisor on a
COMMON tail. Finite modification retains the entire inverse-index l2
error. Uniform o(n) estimates transfer at EVERY COMPLEX source point,
with one neighborhood and cutoff before the whole infinite tail.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem HillHminusDirichletBall.analytic_auxiliaryDisplacement (B : HillHminusDirichletBall) :
    AnalyticOnNhd ℂ (fun a => hillMiuraDirichletDisplacement (B.miuraBall.actionBall.lift a)) B.source := by
  let T : PeriodOneHminusOne → dirichletSubspace (p := 2) := fun a =>
    auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num)
      (hillMiuraDiagonal (B.miuraBall.actionBall.lift a))
  have hT : AnalyticOnNhd ℂ T B.source := fun a ha =>
    ((auxiliaryPeriodOneDirichletPotential (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)).analyticAt _).comp
      (f := fun b => hillMiuraDiagonal (B.miuraBall.actionBall.lift b))
      ((hillMiuraDiagonal.analyticAt _).comp (f := B.miuraBall.actionBall.lift)
        (B.miuraBall.actionBall.lift_analytic a ha))
  intro a ha
  obtain ⟨_,_,U,hU,_,haU,_,R,_,hbound⟩ := exists_uniform_canonicalBoundaryRoots
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (T a)
  let V := B.source ∩ T ⁻¹' U
  have hV : IsOpen V := hT.continuousOn.isOpen_inter_preimage B.source_open hU
  have hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ
      (fun b => hillMiuraDirichletDisplacement (B.miuraBall.actionBall.lift b) n) V := by
    intro n b hb
    have he : (fun c => hillMiuraDirichletDisplacement (B.miuraBall.actionBall.lift c) n) =
        fun c => hillMiuraDiracDirichlet (B.miuraBall.actionBall.lift c) n-(Real.pi : ℂ)*n :=
      funext (fun c => hillMiuraDirichletDisplacement_apply _ n)
    rw [he]
    exact (B.auxiliary_analytic n b hb.1).sub analyticAt_const
  have hnorm : ∀ b ∈ V, ‖hillMiuraDirichletDisplacement (B.miuraBall.actionBall.lift b)‖ ≤ R := by
    intro b hb
    have hh := (hbound (T b) hb.2 .dirichlet).2
    simpa only [T,hillMiuraDirichletDisplacement,sourceAuxiliaryBoundaryDisplacement,sourceBoundaryDisplacement,
      auxiliaryPeriodOneDirichletPotential_eq_sourcePhase] using hh
  exact (Coeff.analyticOnNhd_of_bounded_coordinatewise _ hV hcoord R hnorm) a ⟨ha,haU⟩

theorem memlp_hillHminusCanonicalDirichlet_inverseIndex_error
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    Memℓp (fun n : ℕ+ => (hillHminusCanonicalDirichlet n q-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℕ)) 2 := by
  obtain ⟨N,U,_,_,hqU,_,hcomp⟩ := exists_hillHminusCanonicalDirichlet_uniform_high_comparison q hq
  have hs : ((fun n : ℕ+ => (n : ℕ)) ⁻¹' Iio N).Finite :=
    (Set.finite_Iio N).preimage (fun _ _ _ _ he => PNat.coe_injective he)
  apply NLS.memℓp_of_eq_outside_finset_on (memlp_hillHminusDirichletComplexLabels_inverseIndex_error q) hs.toFinset
  intro n hn
  have hnot : ¬ (n : ℕ) < N := by
    simpa only [Set.Finite.mem_toFinset,mem_preimage,mem_Iio] using hn
  rw [hcomp n (by omega) hqU]

theorem exists_uniform_small_hillHminusCanonicalDirichletDisplacement
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne, 0 < N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalDirichletDomain ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∀ a ∈ U,
        ‖hillHminusCanonicalDirichlet n a-((Real.pi : ℂ)*(n : ℕ))^2‖ < delta*(n : ℝ) := by
  obtain ⟨L,V,hL,hV,hqV,hVD,hcomp⟩ := exists_hillHminusCanonicalDirichlet_uniform_high_comparison q hq
  obtain ⟨M,T,_,hT,hqT,hsmall⟩ := exists_uniform_small_hillHminusDirichletDisplacement q hd
  refine ⟨max L (M+1),V ∩ T,hL.trans_le (le_max_left _ _),hV.inter hT,⟨hqV,hqT⟩,
    (fun a ha => hVD ha.1),?_⟩
  intro n hn a ha
  have hnL : L ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnM : M < (n : ℕ) := by have h := (le_max_right L (M+1)).trans hn; omega
  rw [hcomp n hnL ha.1]
  exact hsmall a ha.2 n hnM

end NLS.KdV
