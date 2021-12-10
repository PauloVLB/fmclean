lemma one_add_le_self (x : mynat) : x ≤ 1 + x :=
begin
rw le_iff_exists_add,
use 1,
rw add_comm,
end