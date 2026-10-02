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
    ext x
    calc
      f x = x • f 1 := by
        simpa using f.map_smul x (1 : K)
      _ = 0 := by simp [h]
      _ = (0 : K →ₗ[K] V) x := rfl
  intro x y hxy
  have hz : f (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hs : (x - y) • f 1 = 0 := by
    simpa using hz
  rcases smul_eq_zero.mp hs with hxy0 | h10
  · exact sub_eq_zero.mp hxy0
  · exact (h1 h10).elim

end MetaEngine
