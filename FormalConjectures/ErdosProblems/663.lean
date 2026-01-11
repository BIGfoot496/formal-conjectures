/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 663
*Reference:* [erdosproblems.com/663](https://www.erdosproblems.com/663)
-/


namespace Erdos663

/--
Let q(n,k) denote the least number coprime to all numbers in [n+1, n+k].
-/

def q (n k : ℕ+) : ℕ :=
    have h : ∃ q > 1, (∀ i ∈ Finset.Icc (n+1) (n+k), q.Coprime i) := by
        use (Nat.exists_infinite_primes (n+k+1)).choose
        have h1 := (Nat.exists_infinite_primes (n+k+1)).choose_spec
        obtain ⟨hl,hr⟩ := h1
        simp only [gt_iff_lt, Finset.mem_Icc, and_imp]
        constructor
        nth_rw 1 [←PNat.one_add_natPred] at hl
        linarith
        intros i _ h2
        have h3 : i < (Nat.exists_infinite_primes (n+k+1)).choose := by
            rw [←PNat.coe_le_coe i (n+k)] at h2
            linarith
        exact Nat.coprime_of_lt_prime (PNat.pos i) h3 hr
    Nat.find h

/--
Is it true that, if k is fixed and n is sufficiently large, we have
q(n,k) < (1 + o(1)) log n?
-/
@[category research open, AMS 11]
theorem erdos_663 :
    answer(sorry) ↔ ∀ k : ℕ+, q (k := k) <ᶠ[.atTop] Nat.log2 n := by
    sorry

end Erdos663
