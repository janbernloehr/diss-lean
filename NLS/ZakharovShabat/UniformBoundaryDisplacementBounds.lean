import NLS.ZakharovShabat.UniformBoundaryRootLabeling
import NLS.ZakharovShabat.UniformSpectralDisplacements
import NLS.ZakharovShabat.CompleteParityDisplacementBounds
import NLS.SequenceSpaces.PairedTailBounds

/-!
# Common bounds for complete boundary root displacements
Each distant boundary root is one of the two original periodic roots in its
disc. Their bounded displacement norms control the boundary tail; the common
central box bounds every possible central enumeration.
-/

noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Central box bounds and membership in a displaced pair bound a complete boundary sequence. -/
theorem BoundaryRootLabeling.norm_displacement_le_of_distant_pair {b : BoundaryCondition} {hp : p ≠ ⊤}
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N ξ) (B : ℝ) (hB : ∀ z ∈ centralSpectralBox N, ‖z‖ ≤ B)
    (a c : Coeff p) (hpair : ∀ n : ℤ, N < n.natAbs →
      ξ n-(Real.pi : ℂ)*n = a n ∨ ξ n-(Real.pi : ℂ)*n = c n) :
    ‖(⟨_,h.displacement⟩ : Coeff p)‖ ≤
      (Finset.Icc (-(N : ℤ)) N).card*(B+Real.pi*N)+(‖a‖+‖c‖) := by
  let d : Coeff p := ⟨_,h.displacement⟩
  let s := Finset.Icc (-(N : ℤ)) N
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have ht : ‖d-Coeff.truncate s d‖ ≤ ‖a‖+‖c‖ :=
    (Coeff.norm_sub_truncate_le_of_mem_pair a c d s (fun n hn => hpair n (by
      simp only [s,Finset.mem_Icc] at hn; omega))).trans
      (add_le_add (Coeff.norm_sub_truncate_le hp0 s a) (Coeff.norm_sub_truncate_le hp0 s c))
  apply (Coeff.norm_le_of_eq_outside_finset d (d-Coeff.truncate s d) s (B+Real.pi*N) ?_ ?_).trans
    (add_le_add le_rfl ht)
  · intro n hn
    have hnN : n.natAbs ≤ N := by simp only [s,Finset.mem_Icc] at hn; omega
    have hc : ‖(Real.pi : ℂ)*n‖ ≤ Real.pi*N := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      rw [← Int.cast_abs,← Int.natCast_natAbs]
      exact_mod_cast hnN
    exact (norm_sub_le (ξ n) ((Real.pi : ℂ)*n)).trans (add_le_add (hB _ (h.central_mem n hnN)) hc)
  · intro n hn
    simp only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,if_neg hn,sub_zero]

/-- Complete labels for both boundary spectra have uniformly bounded full lp norms on one neighborhood. -/
theorem exists_uniform_bounded_boundaryRootLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (dirichletSubspace (p := p)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧
        ∀ ψ ∈ U, ∀ b : BoundaryCondition, ∃ ξ : ℤ → ℂ, ∃ h : BoundaryRootLabeling b hp ψ.val ψ.property N ξ,
          ‖(⟨_,h.displacement⟩ : Coeff p)‖ ≤ R := by
  let F : dirichletSubspace (p := p) →L[ℂ] WeightedCoeffPair SpectralWeight.one.toWeight p :=
    unitBaseEquiv.symm.toContinuousLinearMap.comp (dirichletSubspace (p := p)).subtypeL
  have hF (ψ : dirichletSubspace (p := p)) : weightedBaseToPair SpectralWeight.one (F ψ) = ψ.val := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply ψ.val
  obtain ⟨Nc,V,hNc,hVo,hVc,hVφ,hV0,hcount,_⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  obtain ⟨_,_,W,hWo,hWc,hWφ,hW0,hdisp⟩ := exists_uniform_boundaryDisplacementSummability hp hp1 φ
  obtain ⟨Np,_,T,hTo,hTc,hTφ,hT0,R,hR,hdata⟩ :=
    exists_uniform_bounded_periodicDisplacements hp hp1 SpectralWeight.one (F φ)
  let N := max Nc Np
  obtain ⟨B,hB,hbox⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  let S := (Finset.Icc (-(N : ℤ)) N).card*(B+Real.pi*N)+2*R
  refine ⟨N,hNc.trans_le (le_max_left _ _),(V ∩ W) ∩ (F ⁻¹' T),
    (hVo.inter hWo).inter (hTo.preimage F.continuous),
    (hVc.inter hWc).inter (hTc.linear_preimage (F.restrictScalars ℝ).toLinearMap),
    ⟨⟨hVφ,hWφ⟩,hTφ⟩,⟨⟨hV0,hW0⟩,by simpa only [mem_preimage,map_zero] using hT0⟩,
    S,by dsimp [S]; positivity,?_⟩
  intro ψ hψ b
  obtain ⟨α,β,hα,hβ,ha,hb,_,hpair,_⟩ := hdata (F ψ) hψ.2
  have hc := hcount ψ hψ.1.1 N (le_max_left _ _)
  obtain ⟨ξ,hξ⟩ := exists_boundaryRootLabeling b hp ψ.val ψ.property N hc (hdisp ψ hψ.1.2 b).1
  refine ⟨ξ,hξ,?_⟩
  apply (hξ.norm_displacement_le_of_distant_pair B hbox ⟨_,hα⟩ ⟨_,hβ⟩ ?_).trans
    (add_le_add le_rfl (by linarith))
  intro n hn
  have hd := hξ.distant_spec n hn
  have hs := (hpair n ((le_max_right Nc Np).trans_lt hn)).spectrum_iff (ξ n)
    (refinedResonantDisk_subset_strip n hd.1)
  rw [hF] at hs
  have hz := b.spectrum_subset_periodic hp ψ.val ψ.property ((hξ.exhaustive _).mpr ⟨n,rfl⟩)
  rcases hs.mp hz with he | he
  · exact Or.inl (congrArg (fun z => z-(Real.pi : ℂ)*n) he)
  · exact Or.inr (congrArg (fun z => z-(Real.pi : ℂ)*n) he)

end NLS.ZakharovShabat
