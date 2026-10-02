import Mathlib

namespace MetaEngine

/-- Exact RH cancellation factorization: the observable defect is the distance
of the relative correction E/M from 1. -/
theorem rhCancelFactor (M E : ℂ) (hM : M ≠ 0) :
    M - E = M * (1 - E / M) := by
  field_simp [hM]

/-- Norm form of the exact RH cancellation factorization. -/
theorem rhCancelNorm (M E : ℂ) (hM : M ≠ 0) :
    ‖M - E‖ = ‖M‖ * ‖1 - E / M‖ := by
  rw [rhCancelFactor M E hM, norm_mul]

/-- Centering identity behind the Hodge quadratic-centralizer reduction.
It is purely algebraic and independent of any existence claim for the
correspondence A. -/
theorem quadraticCenteringIdentity {R : Type*} [CommRing R] (x t d : R) :
    (2 * x - t) ^ 2 =
      4 * (x ^ 2 - t * x + d) + (t ^ 2 - 4 * d) := by
  ring

/-- If x satisfies x² - tx + d = 0, then the centered generator
2x - t has square equal to the discriminant t² - 4d. -/
theorem quadraticCenteringOfRelation {R : Type*} [CommRing R]
    (x t d : R)
    (hquad : x ^ 2 - t * x + d = 0) :
    (2 * x - t) ^ 2 = t ^ 2 - 4 * d := by
  rw [quadraticCenteringIdentity, hquad]
  ring

/-- Square-class-2 specialization: once the discriminant is 2*s² and s is a
unit, normalization produces an element whose square is exactly 2. -/
theorem quadraticSqrtTwoOfDiscriminant
    {K : Type*} [Field K]
    (x t d s : K)
    (hs : s ≠ 0)
    (hquad : x ^ 2 - t * x + d = 0)
    (hdisc : t ^ 2 - 4 * d = 2 * s ^ 2) :
    (((2 * x - t) / s) ^ 2) = 2 := by
  rw [div_pow, quadraticCenteringOfRelation x t d hquad, hdisc]
  field_simp [hs]

/-- Quantifier firewall for P-vs-NP meta-analysis:
per-length realizability does not imply one uniform realizer. -/
theorem perLengthExists_not_uniform :
    ∃ R : ℕ → ℕ → Prop,
      (∀ n, ∃ m, R n m) ∧ ¬ (∃ m, ∀ n, R n m) := by
  refine ⟨fun n m => n = m, ?_, ?_⟩
  · intro n
    exact ⟨n, rfl⟩
  · rintro ⟨m, hm⟩
    have h := hm (m + 1)
    omega

/-- A nonzero linear map out of the scalar line is injective.
This is the abstract one-dimensional step used by the BSD BIREAL2 gate after
the common line and realization map have independently been constructed. -/
theorem scalarLine_nonzero_linearMap_injective
    {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (f : K →ₗ[K] V)
    (hf : f ≠ 0) :
    Function.Injective f := by
  have h1 : f 1 ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro x
    calc
      f x = f (x • (1 : K)) := by simp
      _ = x • f 1 := f.map_smul x (1 : K)
      _ = 0 := by simp [h]
      _ = (0 : K →ₗ[K] V) x := rfl
  intro x y hxy
  have hz : f (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hrep : f (x - y) = (x - y) • f 1 := by
    calc
      f (x - y) = f ((x - y) • (1 : K)) := by simp
      _ = (x - y) • f 1 := f.map_smul (x - y) (1 : K)
  rw [hrep] at hz
  rcases smul_eq_zero.mp hz with hxy0 | h10
  · exact sub_eq_zero.mp hxy0
  · exact (h1 h10).elim


/-- RH amplitude-gap return: a strict radial separation from the unit point
forces a quantitative cancellation defect. -/
theorem rhAmplitudeGap_to_defect
    (z : ℂ) (δ : ℝ)
    (hgap : ‖z‖ ≤ 1 - δ) :
    δ ≤ ‖(1 : ℂ) - z‖ := by
  have htri : (1 : ℝ) - ‖z‖ ≤ ‖(1 : ℂ) - z‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) z
  linarith

/-- RH source-facing amplitude-gap return after substituting z = E/M. -/
theorem rhAmplitudeGap_to_residual
    (M E : ℂ) (δ : ℝ)
    (hM : M ≠ 0)
    (hgap : ‖E / M‖ ≤ 1 - δ) :
    δ * ‖M‖ ≤ ‖M - E‖ := by
  have hdef : δ ≤ ‖(1 : ℂ) - E / M‖ :=
    rhAmplitudeGap_to_defect (E / M) δ hgap
  rw [rhCancelNorm M E hM]
  nlinarith [norm_nonneg M]

/-- BSD calibration corollary: one independently nonzero image already proves
injectivity of a linear realization from the scalar line. -/
theorem scalarLine_calibration_injective
    {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    (f : K →ₗ[K] V)
    (η : K)
    (hη : f η ≠ 0) :
    Function.Injective f := by
  apply scalarLine_nonzero_linearMap_injective f
  intro hf
  subst f
  simp at hη


/-- RH absolute amplitude-gap form: if the correction is smaller than the
main term by a relative factor δ, reverse triangle inequality gives the
residual lower bound directly, without dividing by M. -/
theorem rhAbsoluteAmplitudeGap_to_residual
    (M E : ℂ) (δ : ℝ)
    (hgap : ‖E‖ ≤ (1 - δ) * ‖M‖) :
    δ * ‖M‖ ≤ ‖M - E‖ := by
  have hrev : ‖M‖ - ‖E‖ ≤ ‖M - E‖ :=
    norm_sub_norm_le M E
  nlinarith

/-- Scalar-only centralizer actions have zero quadratic discriminant.
Hence the already-known scalar Hecke/F-action cannot by itself satisfy the
nonzero square-class-2 Hodge gate. -/
theorem scalarCentralizer_discriminant_zero
    {K : Type*} [CommRing K] (a : K) :
    (2 * a) ^ 2 - 4 * (a ^ 2) = 0 := by
  ring

/-- Over an ordered field, a scalar-only action cannot have discriminant
2*s² with s nonzero. -/
theorem scalarCentralizer_not_disc_two_square
    {K : Type*} [LinearOrderedField K]
    (a s : K) (hs : s ≠ 0) :
    (2 * a) ^ 2 - 4 * (a ^ 2) ≠ 2 * s ^ 2 := by
  rw [scalarCentralizer_discriminant_zero]
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  nlinarith

end MetaEngine
