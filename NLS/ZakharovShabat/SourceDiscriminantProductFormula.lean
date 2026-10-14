import NLS.ZakharovShabat.FiniteDiscriminant
import NLS.ZakharovShabat.PeriodicEndpointProducts

/-!
# Literal discriminant products on original source potentials

The parity products use actual counted roots, including central roots in
their correct parity sectors. The full product also uses the canonical
lexicographic endpoints. Limits are locally uniform on the whole plane.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Counted actual parity roots give both corrected literal products on the source. -/
theorem exists_sourceDiscriminant_parity_products (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm (periodOnePotential φ)) N ξ η ∧
      TendstoLocallyUniformlyOn (fun M z => evenSpectralPairCutoff ξ η z M)
        (fun z => canonicalDiscriminant hp (periodOnePotential φ) z-2) atTop univ ∧
      TendstoLocallyUniformlyOn (fun M z => oddSpectralPairCutoff ξ η z M)
        (fun z => canonicalDiscriminant hp (periodOnePotential φ) z+2) atTop univ := by
  let ψ := unitBaseEquiv.symm (periodOnePotential φ)
  have he : weightedBaseToPair SpectralWeight.one ψ = periodOnePotential φ := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply _
  obtain ⟨N,_,U,_,_,hψ,_,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 SpectralWeight.one ψ
  obtain ⟨ξ,η,D⟩ := h ψ hψ (by rw [he]; exact periodOnePotential_mem φ) N le_rfl
  have hc := D.canonicalParity_eq_products hp1
  rw [he] at hc
  have hf : evenSpectralPairProduct ξ η = fun z => canonicalDiscriminant hp (periodOnePotential φ) z-2 :=
    hc.1.symm.trans (funext (canonicalEven_eq_discriminant_sub_two hp _))
  have hg : oddSpectralPairProduct ξ η = fun z => canonicalDiscriminant hp (periodOnePotential φ) z+2 :=
    hc.2.symm.trans (funext (canonicalOdd_eq_discriminant_add_two_finite hp hp1 _ (periodOnePotential_mem φ)))
  refine ⟨N,ξ,η,D,?_,?_⟩
  · rw [← hf]
    exact tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η D.left_displacement D.right_displacement
  · rw [← hg]
    exact tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η D.left_displacement D.right_displacement

/-- The literal full product uses the source's globally ordered periodic endpoints. -/
theorem sourceDiscriminant_ordered_product (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    TendstoLocallyUniformlyOn (fun M z => spectralPairPartialProduct
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)) z M)
      (fun z => (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4) atTop univ := by
  have h := tendstoLocallyUniformlyOn_entireSpectralPairProduct hp
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
    (lp.memℓp (canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)))
    (lp.memℓp (canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)))
  rw [canonicalPeriodicEndpoints_product] at h
  convert h using 1
  funext z
  exact (canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 _ (periodOnePotential_mem φ) z).symm

/-- The printed -2 and +2 prefactors still have literal limits; their shifts are incompatible. -/
theorem exists_sourceDiscriminant_printed_parity_limits (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm (periodOnePotential φ)) N ξ η ∧
      TendstoLocallyUniformlyOn
        (fun (M : ℕ) z => -2*∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η z (2*n))
        (fun z => 2*(canonicalDiscriminant hp (periodOnePotential φ) z-2)) atTop univ ∧
      TendstoLocallyUniformlyOn
        (fun (M : ℕ) z => 2*∏ n ∈ Finset.Icc (-(M : ℤ)) M, spectralPairFactor ξ η z (2*n+1))
        (fun z => (canonicalDiscriminant hp (periodOnePotential φ) z+2)/2) atTop univ := by
  obtain ⟨N,ξ,η,D,hf,hg⟩ := exists_sourceDiscriminant_parity_products hp hp1 φ
  have htwo : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => (2 : ℂ))
      (fun _ => 2) atTop univ :=
    (tendsto_const_nhds.tendstoUniformlyOn_const univ).tendstoLocallyUniformlyOn
  have hc := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ)).continuousOn
  refine ⟨N,ξ,η,D,?_,?_⟩
  · have h := htwo.mul₀ hf continuousOn_const (hc.sub continuousOn_const)
    exact h.congr (fun M z _ => by
      dsimp only [Pi.mul_apply,evenSpectralPairCutoff]
      ring)
  · have h := hg.div₀ htwo (hc.add continuousOn_const) continuousOn_const (by intros; norm_num)
    exact h.congr (fun M z _ => by
      dsimp only [Pi.div_apply,oddSpectralPairCutoff]
      ring)

end NLS.ZakharovShabat
