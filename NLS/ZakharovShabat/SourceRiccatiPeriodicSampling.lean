import NLS.ZakharovShabat.SobolevRiccatiPerturbedLattice
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds
import NLS.ZakharovShabat.SourceHigherSobolevEmbedding

/-! # Riccati density sampling at both actual periodic endpoints

Both canonical periodic endpoint sequences admit locally bounded L2 density samples near every complex Hs source, including N=s and H0.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Full endpoint displacement norms are bounded on a common source neighborhood. -/
theorem exists_local_source_periodic_displacement_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ D : ℝ, 0 ≤ D ∧
      ∀ ψ ∈ V,
        ‖canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)‖ ≤ D ∧
        ‖canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)‖ ≤ D := by
  obtain ⟨_,_,U,hU,_,hφ,_,D,hD,hdata⟩ :=
    exists_uniform_small_canonicalPeriodicDisplacements hp hp1
      (periodOnePotential φ) (by norm_num : (0:ℝ) < 1)
  refine ⟨periodOnePotential ⁻¹' U,hU.preimage (periodOnePotential (p := p)).continuous,hφ,D,hD,?_⟩
  intro ψ hψ
  exact ⟨(hdata (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)).1,
    (hdata (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)).2.1⟩

/-- Full periodic endpoint displacement norms are locally bounded on
an original complex Sobolev neighborhood, without choosing continuous labels. -/
theorem exists_local_higherSobolev_periodic_displacement_bounds
    (s : ℕ) (a₀ : SobolevSource s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀ ∈ U ∧
      ∃ R D : ℝ, 0 ≤ R ∧ 0 ≤ D ∧ ∀ ab ∈ U, ‖ab‖ ≤ R ∧
        ‖canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab))
          (periodOnePotential_mem (higherSobolevSourceInclusion s ab))‖ ≤ D ∧
        ‖canonicalPeriodicRightDisplacement (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab))
          (periodOnePotential_mem (higherSobolevSourceInclusion s ab))‖ ≤ D := by
  let F := higherSobolevSourceInclusion s
  have hF : Continuous F := F.continuous
  obtain ⟨V,hV,haV,D,hD,hdata⟩ :=
    exists_local_source_periodic_displacement_bounds (by norm_num) (by norm_num) (F a₀)
  let R := ‖a₀‖+1
  let U : Set (SobolevSource s) := (F ⁻¹' V) ∩ {ab | ‖ab‖ < R}
  have hU : IsOpen U := (hV.preimage hF).inter
    (isOpen_lt continuous_norm continuous_const)
  have haU : a₀ ∈ U := ⟨haV,by dsimp [R]; linarith⟩
  refine ⟨U,hU,haU,R,D,by dsimp [R]; positivity,hD,?_⟩
  intro ab hab
  exact ⟨hab.2.le,hdata (F ab) hab.1⟩

/-- Both canonical periodic endpoint samples of the actual Riccati density
have one L2 bound on a complex neighborhood of every original Hs source.
The two endpoint labels need not be individually analytic or continuous. -/
theorem exists_local_sobolevRiccati_periodic_sample_bound
    (s N : ℕ) (hNs : N ≤ s) (a₀ : SobolevSource s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀ ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab ∈ U, ∀ a b : ℝ → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∃ cL cR : NLS.Coeff 2,
        (∀ n, cL n = ∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*canonicalPeriodicLeft (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n*x)) ∧
        (∀ n, cR n = ∫ x in (0:ℝ)..1, nlsRiccatiDensity a b N x*
          exp (-2*I*canonicalPeriodicRight (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab))
            (periodOnePotential_mem (higherSobolevSourceInclusion s ab)) n*x)) ∧
        ‖cL‖ ≤ C ∧ ‖cR‖ ≤ C := by

  obtain ⟨U,hU,haU,R,D,hR,hD,hdata⟩ := exists_local_higherSobolev_periodic_displacement_bounds s a₀
  obtain ⟨C,hC,h⟩ := exists_uniform_sobolevRiccati_perturbed_lattice_bound s N hNs R hR D hD
  refine ⟨U,hU,haU,C,hC,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨habR,hl,hr⟩ := hdata ab hab
  let Φ := periodOnePotential (higherSobolevSourceInclusion s ab)
  have heven : Φ ∈ pairParitySubspace 0 := periodOnePotential_mem (higherSobolevSourceInclusion s ab)
  obtain ⟨cL,hcL,hnL⟩ := h ab habR a b ha hb hpa hpb hca hcb
    (canonicalPeriodicLeftDisplacement (by norm_num) (by norm_num) Φ heven) hl
  obtain ⟨cR,hcR,hnR⟩ := h ab habR a b ha hb hpa hpb hca hcb
    (canonicalPeriodicRightDisplacement (by norm_num) (by norm_num) Φ heven) hr
  refine ⟨cL,cR,?_,?_,hnL,hnR⟩
  · intro n
    have he (w : ℂ) : (Real.pi:ℂ)*n+(w-(Real.pi:ℂ)*n) = w := by ring
    simpa only [canonicalPeriodicLeftDisplacement_apply,he] using hcL n
  · intro n
    have he (w : ℂ) : (Real.pi:ℂ)*n+(w-(Real.pi:ℂ)*n) = w := by ring
    simpa only [canonicalPeriodicRightDisplacement_apply,he] using hcR n

end NLS.ZakharovShabat
