import ProximityPrize.SubmissionUpper.HalfRadiusCollision

namespace ProximityPrize.SubmissionUpper.IndependentDotFibers

open scoped BigOperators
open HalfRadiusCollision

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Every affine fiber of a nonzero dot-product functional has exactly the
same size as its zero fiber. The zero-fiber count is reused from the discovered
research report, rather than reproved. -/
theorem dot_fiber_card_mul {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) (b : F) :
    (Finset.univ.filter fun v : Fin k → F => dot d v = b).card * Fintype.card F =
      Fintype.card (Fin k → F) := by
  classical
  let φ : (Fin k → F) →+ F :=
    { toFun := dot d
      map_zero' := by simp [dot]
      map_add' := by
        intro x y
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hsurj : Function.Surjective φ := dot_surjective hd
  have hfiber :
      (Finset.univ.filter fun v : Fin k → F => dot d v = b).card =
        (Finset.univ.filter fun v : Fin k → F => dot d v = 0).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj b) (hsurj 0)
  rw [hfiber]
  exact dot_zero_fiber_card_mul hd

/-- A prescribed set of outputs captures exactly its fraction of all vectors.
This permits counting arbitrary forbidden values, not only the zero value. -/
theorem dot_mem_card_mul {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) (B : Finset F) :
    (Finset.univ.filter fun v : Fin k → F => dot d v ∈ B).card * Fintype.card F =
      B.card * Fintype.card (Fin k → F) := by
  classical
  let S := Finset.univ.filter fun v : Fin k → F => dot d v ∈ B
  have hpartition : S.card = ∑ b ∈ B, (S.filter fun v => dot d v = b).card :=
    Finset.card_eq_sum_card_fiberwise (s := S) (t := B) (f := dot d)
      (fun v hv => (Finset.mem_filter.mp hv).2)
  have hfiber (b : F) (hb : b ∈ B) :
      (S.filter fun v => dot d v = b) =
        (Finset.univ.filter fun v : Fin k → F => dot d v = b) := by
    ext v
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hb, h⟩
  change S.card * Fintype.card F = _
  rw [hpartition, Finset.sum_mul]
  calc
    (∑ b ∈ B, (S.filter fun v => dot d v = b).card * Fintype.card F) =
        ∑ _b ∈ B, Fintype.card (Fin k → F) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [hfiber b hb]
      exact dot_fiber_card_mul hd b
    _ = B.card * Fintype.card (Fin k → F) := by simp

/-- For distinct vectors, the difference of their dot products is uniform:
any set of forbidden collision offsets has the exact cardinality below. -/
theorem dot_difference_mem_card_mul {k : ℕ} {x z : Fin k → F}
    (hxz : x ≠ z) (B : Finset F) :
    (Finset.univ.filter fun v : Fin k → F => dot x v - dot z v ∈ B).card *
        Fintype.card F = B.card * Fintype.card (Fin k → F) := by
  have h := dot_mem_card_mul (sub_ne_zero.mpr hxz) B
  simpa only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using h

end ProximityPrize.SubmissionUpper.IndependentDotFibers
