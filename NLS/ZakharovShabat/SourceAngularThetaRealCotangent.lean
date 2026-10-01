import NLS.ZakharovShabat.SourceRealCotangent
import NLS.ZakharovShabat.SourceAngularThetaThetaDiscriminantVariation

/-! # Reality of the actual angle cotangents and their spectral bracket

Constructed real local angle representatives supply real cotangents.
The actual angle/angle bracket and its derivative consequently preserve
reality. Pairing that derivative with a real-parameter discriminant
cotangent makes the entire spectral variation real on the real axis.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual discriminant cotangent is real at every real source
and real spectral parameter. -/
theorem isSourceRealCotangent_sourceDiscriminantCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (x : ℝ) :
    IsSourceRealCotangent (sourceDiscriminantCotangent hp (x:ℂ) φ.val) := by
  apply isSourceRealCotangent_fderiv_of_eventually_real _ φ
  · exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 ((x:ℂ),φ.val) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => ((x:ℂ),ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  · exact Eventually.of_forall (fun ψ hψ => canonicalDiscriminant_im_eq_zero_of_realType
      hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hψ) x)

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Actual real local representatives give reality of the single
theta cotangent for every finite source exponent greater than one. -/
theorem isSourceRealCotangent_thetaDifferential
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    IsSourceRealCotangent (sourceAngularThetaDifferential hp hp1 n s φ.val) := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,E,hA,hreal⟩ :=
    D.exists_local_analytic_real_representative n φ.val (D.real_subset φ.property) hgap
  rw [E.thetaDifferential_eq_fderiv_representative
    ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)) φ.val hφU]
  apply isSourceRealCotangent_fderiv_of_eventually_real _ φ (hA φ.val hφU).differentiableAt
  filter_upwards [E.angle.source_open.mem_nhds hφU] with ψ hψ
  exact hreal ψ hψ

/-- The actual angle/angle bracket is real on the joint open-gap real locus. -/
theorem thetaThetaBracket_im_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (sourceAngularThetaThetaBracket hp hp1 h2p n m s φ.val).im = 0 :=
  sourceBivector_im_eq_zero_of_real_cotangents h2p _ _
    (D.isSourceRealCotangent_thetaDifferential n φ hn) (D.isSourceRealCotangent_thetaDifferential m φ hm)

/-- The actual scalar angle/angle bracket has a real source cotangent. -/
theorem isSourceRealCotangent_thetaTheta_fderiv
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    IsSourceRealCotangent (fderiv ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val) := by
  have hφ := D.real_subset φ.property
  apply isSourceRealCotangent_fderiv_of_eventually_real _ φ
    (D.analyticOnNhd_thetaThetaBracket h2p n m φ.val ⟨⟨hφ,hn⟩,⟨hφ,hm⟩⟩).differentiableAt
  filter_upwards [(D.open_gap n).mem_nhds ⟨hφ,hn⟩,(D.open_gap m).mem_nhds ⟨hφ,hm⟩] with ψ hψn hψm
  intro hreal
  exact D.thetaThetaBracket_im_eq_zero h2p n m ⟨ψ,hreal⟩ hψn.2 hψm.2

/-- The entire actual discriminant variation of the angle/angle
bracket is real on the real spectral axis. -/
theorem thetaThetaDiscriminant_im_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (x : ℝ) :
    (sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val (x:ℂ)).im = 0 :=
  sourceBivector_im_eq_zero_of_real_cotangents h2p _ _
    (D.isSourceRealCotangent_thetaTheta_fderiv h2p n m φ hn hm)
    (isSourceRealCotangent_sourceDiscriminantCotangent hp hp1 φ x)

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
