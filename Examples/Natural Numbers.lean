import data.nat.basic

example (a : ℕ ): a + 0 = a:=
begin
induction a with k hk,
rw zero_add,
rw add_zero,
end