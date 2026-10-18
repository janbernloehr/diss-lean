import NLS.ZakharovShabat.SobolevFiniteBoundExtension
import NLS.ZakharovShabat.SobolevHamiltonianPhase
import NLS.ZakharovShabat.SobolevDiscriminantUniformAsymptotics
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.SourceHigherSobolevEmbedding

/-! # Uniform discriminant asymptotics for all Sobolev sources

The actual canonical discriminant has a Hamiltonian approximation uniform on complex Hs balls, including nonsmooth sources, for s >= 1 and N <= s.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Finite Fourier inclusion preserves every original source coefficient. -/
theorem higherSobolevSourceInclusion_ofFinsupp (s : ℕ) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    higherSobolevSourceInclusion s (sobolevSourceOfFinsupp s a) = CoeffPair.ofFinsupp a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n <;> simp [sobolevSourceOfFinsupp]

/-- The actual canonical discriminant has a Hamiltonian approximation
uniform on every original Hs ball, including nonsmooth complex sources. -/
theorem exists_uniform_sourceSobolevDiscriminant_hamiltonian_strip_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        ‖canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) z-
          2*cos (I*sobolevHamiltonianPhase s N hNs ab z)‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨C,hC,h⟩ := exists_uniform_classicalDiscriminant_hamiltonian_strip_error_bound
    s N hs hNs (R+1) (by positivity) H
  refine ⟨C,hC,?_⟩
  intro ab hab z hzn hzH
  let F (cd : SobolevSource s) := ‖canonicalDiscriminant (by norm_num)
    (periodOnePotential (higherSobolevSourceInclusion s cd)) z-
      2*cos (I*sobolevHamiltonianPhase s N hNs cd z)‖
  have hdisc : Continuous (fun cd : SobolevSource s =>
      canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s cd)) z) := by
    have hc : Continuous (fun q : ℂ × CoeffPair 2 =>
        canonicalDiscriminant (by norm_num) (periodOnePotential q.2) q.1) :=
      continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_periodOne
        (p := 2) (by norm_num) (by norm_num)).continuousOn
    have hi : Continuous (fun cd : SobolevSource s => (z, higherSobolevSourceInclusion s cd)) :=
      continuous_const.prodMk (higherSobolevSourceInclusion s).continuous
    exact Continuous.comp
      (g := fun q : ℂ × CoeffPair 2 =>
        canonicalDiscriminant (by norm_num) (periodOnePotential q.2) q.1)
      (f := fun cd : SobolevSource s => (z, higherSobolevSourceInclusion s cd)) hc hi
  have hF : Continuous F := hdisc.sub
    (continuous_const.mul (continuous_cos.comp (continuous_const.mul (continuous_sobolevHamiltonianPhase s N hNs z)))) |>.norm
  apply le_of_finite_sobolev_ball_bound s F hF R (C/(2*‖z‖)^N) _ ab hab
  intro cd hcd
  let a := polynomial cd.1
  let b := polynomial cd.2
  have ha : ContDiff ℝ ∞ a := contDiff_source_polynomial cd.1
  have hb : ContDiff ℝ ∞ b := contDiff_source_polynomial cd.2
  have hpa : Function.Periodic a 1 := periodic_source_polynomial cd.1
  have hpb : Function.Periodic b 1 := periodic_source_polynomial cd.2
  have hca (j : ℤ) : (sobolevSourceOfFinsupp s cd).1.val j = periodOneCoefficient a j := by
    simp [sobolevSourceOfFinsupp,a]
  have hcb (j : ℤ) : (sobolevSourceOfFinsupp s cd).2.val j = periodOneCoefficient b j := by
    simp [sobolevSourceOfFinsupp,b]
  have he := h (sobolevSourceOfFinsupp s cd) hcd a b ha hb hpa hpb hca hcb z hzn hzH
  have hcurve : classicalPotentialOfFunctions a b ha.continuous hb.continuous = finiteSourceCurve cd := by
    apply ContinuousMap.ext
    intro t
    simp [classicalPotentialOfFunctions,finiteSourceCurve,BoundaryCondition.periodOnePair,a,b,polynomial]
  change ‖canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s (sobolevSourceOfFinsupp s cd))) z-
    2*cos (I*sobolevHamiltonianPhase s N hNs (sobolevSourceOfFinsupp s cd) z)‖ ≤ _
  rw [higherSobolevSourceInclusion_ofFinsupp,canonicalDiscriminant_finite_eq_classical,
    sobolevHamiltonianPhase_eq_classical s N hNs (sobolevSourceOfFinsupp s cd) a b ha hb hpa hpb hca hcb]
  rwa [hcurve] at he

end NLS.ZakharovShabat
