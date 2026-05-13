import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic

namespace KRR

/-- 
The number of permutations σ of {0, ..., k-1} such that σ(i) ≤ m(i) 
for all i, where m is a non-decreasing sequence of bounds.
-/
theorem card_perm_le_m {k : ℕ} (m : Fin k → Fin k) (hm : Monotone m) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ∀ i, σ i ≤ m i)).card = 
    Nat.factorial k := -- This is NOT generally true, just a placeholder
  sorry

end KRR
