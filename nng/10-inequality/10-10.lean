lemma le_succ_self (a : mynat) : a ≤ succ a :=
begin
apply le_succ,
exact le_refl a,
end