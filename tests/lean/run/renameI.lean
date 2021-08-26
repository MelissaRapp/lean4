example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
  intros
  renameI h1 _ h2
  apply Eq.trans
  apply Eq.symm
  exact h2
  exact h1
