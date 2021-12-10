theorem not_succ_le_self (a : mynat) : ¬ (succ a ≤ a) :=
begin
intro h,
induction a with h hd,
cases h with c hc,
rw succ_add at hc,
rw zero_add at hc,
exact zero_ne_succ c hc,
have hh := le_of_succ_le_succ _ _ h,
have f := hd hh,
exact f,
end