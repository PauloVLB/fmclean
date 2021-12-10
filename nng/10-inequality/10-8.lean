lemma succ_le_succ (a b : mynat) (h : a ≤ b) : succ a ≤ succ b :=
begin
cases h with c hc,
rw hc,
rw ← succ_add,
use c,
refl,

end