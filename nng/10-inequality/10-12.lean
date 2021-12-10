theorem le_of_succ_le_succ (a b : mynat) : succ a ≤ succ b → a ≤ b :=
begin
intro ab,
cases ab with c hc,
rw succ_add at hc,
rw succ_eq_succ_iff at hc,
use c,
exact hc,

end