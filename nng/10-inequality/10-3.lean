theorem le_succ (a b : mynat) : a ≤ b → a ≤ (succ b) :=
begin
intro h,
cases h with c hc,
rw hc,
rw ← add_succ,
use succ c,
refl,

end