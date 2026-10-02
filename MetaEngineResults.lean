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
  rw [quadraticCenteringIdentity]
  simp [hquad]

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

end MetaEngine
