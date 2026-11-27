import Mathlib

theorem Conjectures.Goldbach.BeaumontResonanceWindow :
    ∀ n p q : ℕ, 0 < n → n ≤ p+q → p+q < 2*n → (n ∣ p+q ↔ p+q=n) := by
  intro n p q hn hlo hhi
  constructor
  · rintro ⟨k, hk⟩
    have : k = 1 := by
      by_contra bad
      rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | hk'
      · simp at hk
        omega
      · have := Nat.mul_le_mul_left n hk'
        omega
    simpa [this] using hk
  · rintro h
    rw [h]
