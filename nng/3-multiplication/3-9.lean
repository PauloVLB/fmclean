lemma mul_left_comm (a b c : mynat) : a * (b * c) = b * (a * c) :=
begin
induction c with h hd,
rw mul_zero,
rw mul_zero,
rw mul_zero,
refl, 
rw mul_succ,
rw mul_succ,
rw mul_comm,
rw mul_add,
rw add_mul,
rw ← hd,
rw mul_comm,
refl,

end