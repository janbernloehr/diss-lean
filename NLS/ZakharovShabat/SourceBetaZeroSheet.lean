import NLS.ZakharovShabat.SourceAngularOriginalBetaValues

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- On the SAME original source domain a zero terminal anti-discriminant
forces the actual chosen beta value to vanish, including low and
collapsed gaps. No regular primitive at the zero sheet is postulated. -/
theorem SourceLemma12_12Data.beta_original_eq_zero_of_sheet_zero
    {hp : p≠⊤} {hp1 : 1<p} {W₀ W : Set (CoeffPair p)}
    {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ∈W)
    (n m : ℤ) (hw : sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m ψ=0) :
    sourceAngularBeta hp hp1 n m s ψ=0 := by
  obtain ⟨C,hμ⟩ := H.angular_original_circles ψ hψ
  have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ m
    ((C m).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ m))) hw
  apply sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ
  simpa only [SourceAngularDirichletTerminalIsEndpoint,mem_insert_iff,mem_singleton_iff] using hend

end NLS.ZakharovShabat
