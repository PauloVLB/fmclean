lemma add_squared (a b : mynat) :
  (a + b) ^ (2 : mynat) = a ^ (2 : mynat) + b ^ (2 : mynat) + 2 * a * b :=
begin
rw two_eq_succ_one,
rw one_eq_succ_zero,
repeat {rw pow_succ},
rw pow_zero,
rw one_mul,
repeat {rw pow_zero},
repeat {rw one_mul},
rw succ_mul,
rw succ_mul,
rw zero_mul,
rw zero_add,
rw mul_add,
repeat {rw add_mul},
simp,

end