import NLS.KdV.HillIsospectralPrimitiveDerivative
import NLS.KdV.HillDirichletFamilyAngle
import NLS.KdV.HillFiniteAbelianTerminalRepresentation

/-! # Actual derivatives of the independent finite Abelian phase

Local differentiable sheeted terminal lifts represent the original phase.
Isospectrality freezes its independently normalized differential; the
actual Dirichlet velocities then determine the phase derivative. Only
the contributing finite set needs interior, nonzero sheets.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hasDerivAt_hillFiniteAbelianPhase_isospectral_family
    (C : ℝ → RealPeriodOneHillPotential) (t0 : ℝ) (hC : ContinuousAt C t0)
    (hQ : DifferentiableAt ℝ (fun t => SpectralWeight.one.toCoeff (C t).val) t0)
    (hl : ∀ t,hillRealLabels (C t).val (C t).property.1 (C t).property.2 =
      hillRealLabels (C t0).val (C t0).property.1 (C t0).property.2)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hnF : n-1 ∈ F)
    (v : ℕ → ℂ)
    (hμ : ∀ k ∈ F,HasDerivAt (fun t =>
      (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 (k+1) (by omega) : ℂ)) (v k) t0)
    (hR : ∀ k ∈ F,hillDirichletSheetRoot (SpectralWeight.one.toCoeff (C t0).val)
      (hillDirichletEnergy (C t0).val (C t0).property.1 (C t0).property.2 (k+1) (by omega)) ≠ 0) :
    let q := C t0
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    HasDerivAt (fun t => hillFiniteAbelianPhase (C t) n hn F)
      (I*hillFiniteAbelianPhase q n hn F*
        ∑ k ∈ F,ψ (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))*v k/
          hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))) t0 := by
  classical
  let q := C t0
  have hgap (k : ℕ) (hk : k ∈ F) : hillRealGapHalfLength q.val q.property.1 q.property.2 (k+1) ≠ 0 := by
    intro hc
    exact hR k hk (hillDirichletSheetRoot_eq_zero_of_halfLength_zero q.val q.property.1 q.property.2 (k+1) (by omega) hc)
  choose θ hθ hterminal using (fun k : F => exists_differentiable_hillDirichlet_family_angle C t0 hC hQ
    (k.val+1) (by omega) (hgap k.val k.property))
  let Θ (k : ℕ) : ℝ → ℝ := if hk : k ∈ F then θ ⟨k,hk⟩ else fun _ => 0
  have hΘ (k : ℕ) (hk : k ∈ F) : DifferentiableAt ℝ (Θ k) t0 := by
    simpa only [Θ,dif_pos hk] using hθ ⟨k,hk⟩
  have hterms : ∀ᶠ t in 𝓝 t0,∀ k ∈ F,
      hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 (k+1) ≠ 0 ∧
      cosineGapPoint (hillRealGapCenter (C t).val (C t).property.1 (C t).property.2 (k+1))
        (hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 (k+1)) (Θ k t : ℂ) =
          (hillDirichletEnergy (C t).val (C t).property.1 (C t).property.2 (k+1) (by omega) : ℂ) ∧
      sin (Θ k t : ℂ) = hillDirichletGapSine (C t).val (C t).property.1 (C t).property.2 (k+1) (by omega) := by
    apply (F.eventually_all).mpr
    intro k hk
    simpa only [Θ,dif_pos hk] using hterminal ⟨k,hk⟩
  let S (t : ℝ) := ∑ k ∈ F,
    hillAbelianCosinePrimitive (C t).val (C t).property.1 (C t).property.2 n hn (k+1) (Θ k t : ℂ)
  have hd (k : ℕ) (hk : k ∈ F) :
      HasDerivAt (fun t => hillAbelianCosinePrimitive (C t).val (C t).property.1 (C t).property.2
        n hn (k+1) (Θ k t : ℂ))
        (hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
          (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))*v k/
            hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
              (hillDirichletEnergy q.val q.property.1 q.property.2 (k+1) (by omega))) t0 := by
    exact hasDerivAt_hillAbelianPrimitive_isospectral_terminal C t0 hl n hn (k+1) (by omega)
      (Θ k) (deriv (Θ k) t0) (hΘ k hk).hasDerivAt
      (hterms.mono (fun _ ht => (ht k hk).2)) (hgap k hk) (v k) (hμ k hk) (hR k hk)
  have hS := HasDerivAt.fun_sum hd
  have he : (fun t => hillFiniteAbelianPhase (C t) n hn F) =ᶠ[𝓝 t0] (fun t => exp (I*S t)) := by
    filter_upwards [hterms] with t ht
    exact hillFiniteAbelianPhase_eq_exp_terminal_primitives (C t) n hn F hnF (fun k => Θ k t)
      (fun k hk => (ht k hk).1) (fun k hk => (ht k hk).2.1) (fun k hk => (ht k hk).2.2)
  have hphase := ((hS.const_mul I).cexp).congr_of_eventuallyEq he
  apply hphase.congr_deriv
  have hbase := Filter.EventuallyEq.eq_of_nhds he
  rw [← hbase]
  ring

end NLS.KdV
